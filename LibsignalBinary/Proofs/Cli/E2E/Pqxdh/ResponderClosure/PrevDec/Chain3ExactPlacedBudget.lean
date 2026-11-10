/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.ChainKeyEpilogue
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Base
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.MergeReceiverChainsAux.Steps
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import ProofLib.SepLogic.WPp

/-!
# Exact-Trace Budget Contract for Handshake `message::merge<Chain>`

Exact-trace (`evs = chainMergeEvents x.c`) total-correctness verification of
`prost::encoding::message::merge::<Chain, &mut &[u8]> [local#4]` (Block `516`, `lsmpl.base 516`)
under `[LibsignalPlacement]`, tracking capacity-pinned `Vec<MessageKey>` growth (`c3x_chain3GAtCap`)
from `0` on entry to `vecCap4Of c.keys.length` on exit.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3ExactPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator maxMessageKeys)
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl withLsCl
)
open CryptoVerification.RustHeap (
  RustAlloc arrayAt arrayAt_concat arrayAt_nil vecAt vecBuf vecHeader vecOf vecU8 vecU8At
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec (
  WireType decodeVarint decodeVarint_encodeVarint encodeVarint mergeBytes
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost DecodeVarintSlowGhost
  bytesMergeCapOk_zero sliceCursorAfter sliceCursorAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced
  lsRustAllocSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliGhostExterns cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_panic_handle_error
)
open CryptoVerification.E2E.Record (pbBytes pbVarint)
open CryptoVerification.E2E.Record.DeserializeSeed (
  chunks104_6QWAt_dst_eq_receiverChains chunks104_6QWAt_entails_memRegion104_receiverChains
  chunks104_6QWAt_stack_eq_receiverChains ckEnc_length_bounds_seedChain
  memRegion104_eq_exists_chunks104_6QWAt_receiverChains mergeBytes_lt128_seedChain
  sliceCursorAfter_append_eq_seedChain
)
open Proofs.libsignal.Hooks2 (
  ule_ofNat_of_gt_false_seedChain62 ult_ofNat_of_gt_true_seedChain62
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainField ChainG ChainMergeGenGhost SegStepG
  chainField_tag_cases chainGAfter chainGAfter_fields
  pbBytes_lt128_eq_seedChain pbBytes_pointsTo_combine_seedChain pbBytes_ptr_advance_seedChain
  prostChainGAt prostMsgKeyAt segStepG_then
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG (
  chainField_ck_enc_eq chainField_tag_three_info combine_tag3_cursor
  payload_append_eq_pfx_rem pfx_k pfx_k_succ rem_k rem_k_eq_cons
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG (
  arrayAt_prostMsgKeyAt_move_bytes beq_ofNat_cap_false chainField_eq_key_of_tag4
  chainGAfter_keys_length_le chainGAfter_succ_of_key chainG_payload_split
  drop_fields_flatMap_enc_of_key encMessageKey_eq_pb encMessageKey_length_lt128
  lenField_4_encMessageKey_eq memRegion_spare_split_of_lt mem_keys_of_key_mem_fields
  ofNat_add_one_eq prostMsgKeyAt_move_chunks104 ptr_madd_104_eq
  sliceCursorAfter_tag4_combine spAligned_of_sp_eq
)
open CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG (
  chainGAfter_succ chainG_enc_eq_fields_local curPtr curPtr_succ drop_flatMap_enc
  lenField_eq_pbBytes mem_fields_priv_length_lt mem_fields_srk_length_lt
  payload_append_eq_preBytes pointsToBytes_preBytes_succ preBytes sliceCursorAfter_eq_preBytes
)
open CryptoVerification.CliHandshake.Placed (blkLib_eq_516 blkPl_516 lsProg_516)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  Chain3InnerLoopRegs Chain3LoopRegsPreserved Chain3MkRegs SepWPp.of_sepWP_lscl_c3
  c3ck_regs_after_call c3k3c_pointsTo_12_combine c3mk_prostMsgKeyAt_fold
  c3mk_push_spAligned c3mk_sp0_aligned_of_sub_240 c3seed_pointsTo_2a_combine
  chain3GAt chain3GAt_entails_prostChainGAt chain3PCPlacedAtW
  chain3SavedRegs chain3SavedRegs_c3mk_split chain3VecAt chain3VecAt_nil_elim
  chain3VecAt_nil_intro chain3VecAt_of_ne_nil chainGRest
  chainMerge3StackX chainMerge3SubStackX default_cells_entail_chain3VecAt
  decodeVarint_0a_cons decodeVarint_12_cons
  extract_withLsCl_post_c3 intro_withLsCl_c3 libsignalCodeLoaded_preserve_c3
  sp0_aligned_of_sub_240_aligned sp0_aligned_of_sub_240_c3
  stackAt_c3Sub_eq_bytesMerge stackAt_c3Sub_to_decodeVarint
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (bytesMerge3Stack)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  fitsEvents_append
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  finishGrowEvents finishGrowStackX framelessMemcpyBudgetSpec framelessMemcpy_hookOk
  noAllocShimBudgetSpec noAllocShim_hookOk
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (
  BytesMergeEnv bytesMergeEventsCore doReserveClearEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env growOne104Events growOne104SpecX growOneChainSpecX
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  le_vecCap4Of vec104GrowEvents vecCap4Next vecCap4Of vecCap4Of_le_pow20 vecCap4Of_succ
  vecCap4Of_zero vecCap4Push
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ProstMergeBudget (
  bytesDropEvents bytesMergeAllocEvents bytesMergeEvents doReserveEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (
  chainDoneEvents chainFieldStepEvents chainGAfter_priv_eq_nil chainGAfter_srk_eq_nil
  chainMergeEvents chainRemEvents chainRemEvents_eq_cons chainRemEvents_zero
  prostChainGAtCap prostMsgKeyAtCap prostMsgKeyAtCap_entails_prostMsgKeyAt vecU8FreshCap
)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.AllocFsA1Budget (CliAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks bumpGhost
  cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_realloc_budget_sat
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget (
  cliAllocHooks_to_bumpGhost
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3RawSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudgetAux (
  ls_externAt?_withPanics_eq sepWPp_mono_pre_c3 step_chain3Exit_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroAPlacedBudget (
  Chain3CalleesCroPlacedW SepWPp.bind_lscro
  c3_dv_call_cro chain3CalleesCro_of_hooks intro_withLsCodeRoLoaded_c3
  sp_sub_240_aligned_c3_cro step_chain3Entry_post_placed_vm step_chain3Entry_pre_placed_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudgetAux (
  c3_outer_head_vm
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroBPlacedBudget (
  c3a_dv_cro pool_eq_of_vm_c3 step_seg3a_cro step_seg3b_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlacedBudgetAux (
  step_c3ihead_placed_vm step_c3seed_icont_placed_vm step_c3seed_key_placed_vm
  step_mkCnt_cro step_mkHead_cro
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

/-! ## Capacity-Pinned `Chain` Representation (`c3x_chain3GAtCap`) and Spatial Bridges -/

/-- The `message_keys` (pinned at capacity `capMk`) and `chain_key` fields of `prostChainGAt A a c`. -/
def c3x_chainGRestCap (A : RustAlloc) (a : BitVec 64) (capMk : Nat) (c : ChainG) : SepProp :=
  (∃∗ ptrMk : BitVec 64,
    vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b)
      (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-- Capacity-pinned `chain3GAt`: `srk` and `priv` as `chain3VecAt` (`cap = 0#64` when `[]`) and
`keys` pinned at capacity `BitVec.ofNat 64 capMk` (`0` on entry, `vecCap4Of c.keys.length` on exit). -/
def c3x_chain3GAtCap (A : RustAlloc) (a : BitVec 64) (capMk : Nat) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ c3x_chainGRestCap A a capMk c

theorem c3x_chainGRestCap_entails_chainGRest (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    c3x_chainGRestCap A a capMk c ⊢ chainGRest A a c := by
  unfold c3x_chainGRestCap chainGRest vecOf
  refine sepConj_mono_left ?_
  refine Entails.sepExists_elim fun ptrMk => ?_
  exact Entails.sepExists_right (BitVec.ofNat 64 capMk)
    (Entails.sepExists_right ptrMk (Entails.refl _))

theorem c3x_chain3GAtCap_entails_chain3GAt (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    c3x_chain3GAtCap A a capMk c ⊢ chain3GAt A a c := by
  unfold c3x_chain3GAtCap chain3GAt
  exact sepConj_mono_right (sepConj_mono_right (c3x_chainGRestCap_entails_chainGRest A a capMk c))

theorem c3x_chain3GAtCap_entails_prostChainGAt (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    c3x_chain3GAtCap A a capMk c ⊢ prostChainGAt A a c :=
  Entails.trans (c3x_chain3GAtCap_entails_chain3GAt A a capMk c)
    (chain3GAt_entails_prostChainGAt A a c)

private theorem c3x_arrayAt_msgKeyCap_entails (A : RustAlloc) :
    ∀ (ks : List MessageKeyGenerator) (ptr : BitVec 64),
      arrayAt (fun mkg b => prostMsgKeyAtCap A mkg b) 104 ptr ks ⊢
        arrayAt (fun mkg b => prostMsgKeyAt A mkg b) 104 ptr ks
  | [], _ => Entails.refl _
  | mkg :: ks, ptr =>
    sepConj_mono (prostMsgKeyAtCap_entails_prostMsgKeyAt A mkg ptr)
      (c3x_arrayAt_msgKeyCap_entails A ks (ptr + BitVec.ofNat 64 104))

theorem c3x_prostChainGAtCap_zero_entails_chain3GAtCap (A : RustAlloc) (a : BitVec 64) :
    prostChainGAtCap A a 0 ChainG.empty ⊢ c3x_chain3GAtCap A a 0 ChainG.empty := by
  unfold prostChainGAtCap c3x_chain3GAtCap c3x_chainGRestCap ChainG.empty vecU8FreshCap
  dsimp only [List.length_nil]
  have hv0 : (∃∗ ptr : BitVec 64, vecU8At A a 0#64 ptr []) ⊢ chain3VecAt A a [] :=
    Entails.sepExists_elim fun ptr => chain3VecAt_nil_intro A a ptr
  have hv1 : (∃∗ ptr : BitVec 64, vecU8At A (a + 0x18#64) 0#64 ptr []) ⊢
      chain3VecAt A (a + 0x18#64) [] :=
    Entails.sepExists_elim fun ptr => chain3VecAt_nil_intro A (a + 0x18#64) ptr
  have hv2 :
      (∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mkg b => prostMsgKeyAtCap A mkg b) (a + 0x30#64) 0#64 ptrMk []) ⊢
      (∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mkg b => prostMsgKeyAt A mkg b) (a + 0x30#64) 0#64 ptrMk []) := by
    refine Entails.sepExists_elim fun ptrMk => Entails.sepExists_right ptrMk ?_
    unfold vecAt vecBuf arrayAt
    exact Entails.refl _
  exact sepConj_mono hv0 (sepConj_mono hv1 (sepConj_mono_left hv2))

/-- `Chain::default()`'s empty `Vec<MessageKey>` cells at `v` (`cap = 0`, `ptr = 8`, `len = 0`)
entail `vecAt` pinned at `cap = 0#64`. -/
theorem c3x_default_cells_entail_c3KeysCap (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      ∃∗ ptrMk : BitVec 64,
        vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b) v 0#64 ptrMk [] := by
  refine Entails.sepExists_right 8#64 ?_
  unfold vecAt vecHeader vecBuf
  have hp : (⌜([] : List MessageKeyGenerator).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0⌝ : SepProp) = emp := by
    simp
  rw [hp]
  simp only [emp_sepConj]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `Chain::default()`'s 10 cells + 24 spare bytes at `a` entail `c3x_chain3GAtCap A a 0 ChainG.empty`. -/
theorem c3x_default_cells_entail_chain3GAtCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ 1#64) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
    ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ 8#64) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
    ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 ⊢
      c3x_chain3GAtCap A a 0 ChainG.empty := by
  have h1 : a + 0x18#64 + 8#64 = a + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have h2 : a + 0x18#64 + 16#64 = a + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  have h3 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have h4 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hv1 := default_cells_entail_chain3VecAt A a
  have hv2 := default_cells_entail_chain3VecAt A (a + 0x18#64)
  have hv3 := c3x_default_cells_entail_c3KeysCap A (a + 0x30#64)
  rw [h1, h2] at hv2
  rw [h3, h4] at hv3
  unfold c3x_chain3GAtCap c3x_chainGRestCap ChainG.empty
  dsimp only
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv3)))
  exact Entails.of_eq (by sep_ac_rfl)

/-- Tag-6 (`sender_chain`, `q + 0x9c0#64`) pre-call bridge into `c3x_chain3GAtCap A (q + 0x9c0#64) 0 ChainG.empty`. -/
theorem c3x_overDecChain_bridge_ext (A : RustAlloc) (q : BitVec 64) :
    ((q + 0x9c0#64) ↦₆₄ 0#64) ∗ ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗
    ((q + 0x9d8#64) ↦₆₄ 0#64) ∗ ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗
    ((q + 0x9f0#64) ↦₆₄ 0#64) ∗ ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
    ((q + 0xa08#64) ↦₆₄ noneCap) ∗ memRegion (q + 0xa10#64) 24 ⊢
      c3x_chain3GAtCap A (q + 0x9c0#64) 0 ChainG.empty := by
  have h := c3x_default_cells_entail_chain3GAtCap A (q + 0x9c0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- Tag-7 (`receiver_chains`, `q + 0xbf0#64`) pre-call bridge into `c3x_chain3GAtCap A (q + 0xbf0#64) 0 ChainG.empty`. -/
theorem c3x_default_cells_bf0_entail_chain3GAtCap_ext (A : RustAlloc) (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      c3x_chain3GAtCap A (q + 0xbf0#64) 0 ChainG.empty := by
  have h := c3x_default_cells_entail_chain3GAtCap A (q + 0xbf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h ⊢
  exact h

/-! ## Exact-Trace Envelope and Block-`516` Specifications -/

/-- Exact deterministic allocator event envelope of `message::merge<Chain>` on `c`. -/
def c3x_ChainMergeExactEnv (c : ChainG) (evs : List AllocEvent) : Prop :=
  evs = chainMergeEvents c

theorem c3x_fitsEnv_exact_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} {c : ChainG} :
    FitsEnv M lim st (c3x_ChainMergeExactEnv c) ↔ FitsEvents M lim st (chainMergeEvents c) := by
  constructor
  · intro h
    exact h (chainMergeEvents c) rfl
  · rintro h _ rfl
    exact h

/-- Capacity-retaining exact-trace raw contract of handshake
`prost::encoding::message::merge::<Chain, &mut &[u8]> [local#4]` (Block `516`, `lsmpl.base 516`)
at `chainMerge3StackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def c3x_chainMerge3ExactCapRawSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents x.c)⌝ ∗
      c3x_chain3GAtCap A.repAlloc x.a 0 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMerge3StackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool lim (M.stepEvents (chainMergeEvents x.c) st) sf ∗ stackAt s0.sp chainMerge3StackX

/-- Exact-trace raw contract of handshake
`prost::encoding::message::merge::<Chain, &mut &[u8]> [local#4]` (Block `516`, `lsmpl.base 516`)
at `chainMerge3StackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`), erasing `c3x_chain3GAtCap` to
`prostChainGAt` in `post` to match `TopPlacedBudgetAux.chainMerge3RawSpecW`. -/
def c3x_chainMerge3ExactRawSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents x.c)⌝ ∗
      c3x_chain3GAtCap A.repAlloc x.a 0 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMerge3StackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A.repAlloc x.a x.c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool lim (M.stepEvents (chainMergeEvents x.c) st) sf ∗ stackAt s0.sp chainMerge3StackX

/-- Relocatable `[LibsignalPlacement]` exact-trace Block-`516` contract on `lsProg_518 ext`
under `withLsCodeRoLoaded lsmpl`, retaining `c3x_chain3GAtCap` in `post`. -/
def c3x_ChainMerge5ExactCapCroPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
    (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim))

/-- Relocatable `[LibsignalPlacement]` exact-trace Block-`516` contract on `lsProg_518 ext` under `withLsCodeRoLoaded lsmpl`, producing `prostChainGAt` in `post`. -/
def c3x_ChainMerge5ExactCroPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
    (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim))

/-! ## Exact-Trace Loop Proof -/

section ExactLoopProof

private theorem c3x_bytesMergeEventsCore_zero_eq {wt : WireType} {bs b rest : List (BitVec 8)}
    (hmB : mergeBytes wt bs = some (b, rest)) :
    bytesMergeEventsCore wt 0#64 bs = bytesMergeEvents 0 b.length := by
  unfold bytesMergeEventsCore doReserveClearEvents bytesMergeEvents bytesMergeAllocEvents
    doReserveEvents bytesDropEvents
  rw [hmB]
  have hz : (0#64 : BitVec 64).toNat = 0 := rfl
  rw [hz]
  by_cases hb0 : b.length = 0
  · simp [hb0]
  · have hpos : 0 < b.length := Nat.pos_of_ne_zero hb0
    have hnle : ¬ b.length ≤ 0 := by omega
    simp [hb0, hpos, hnle, List.append_assoc]

private theorem c3x_vecCap4Of_zero_or_ge4 : ∀ n : Nat, vecCap4Of n = 0 ∨ 4 ≤ vecCap4Of n
  | 0 => Or.inl vecCap4Of_zero
  | n + 1 => by
    rw [vecCap4Of_succ]
    unfold vecCap4Push vecCap4Next
    rcases c3x_vecCap4Of_zero_or_ge4 n with h0 | h4 <;> split_ifs <;> omega

private theorem c3x_vecCap4Of_toNat {n : Nat} (hbound : n ≤ maxMessageKeys) :
    (BitVec.ofNat 64 (vecCap4Of n)).toNat = vecCap4Of n := by
  have hle : vecCap4Of n ≤ 2 ^ 20 := vecCap4Of_le_pow20 (by unfold maxMessageKeys at hbound; omega)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vecCap4Of n < 2 ^ 64)]

private theorem c3x_max_eq_vecCap4Next (n : Nat) :
    max (2 * vecCap4Of n) 4 = vecCap4Next (vecCap4Of n) := by
  rcases c3x_vecCap4Of_zero_or_ge4 n with h0 | h4
  · rw [h0]; rfl
  · have hne : vecCap4Of n ≠ 0 := by omega
    unfold vecCap4Next
    simp only [hne, ↓reduceIte]
    omega

private theorem c3x_growOne104Events_eq {n : Nat} (hbound : n ≤ maxMessageKeys) :
    growOne104Events (BitVec.ofNat 64 (vecCap4Of n)) = vec104GrowEvents (vecCap4Of n) := by
  unfold growOne104Events finishGrowEvents vec104GrowEvents
  rw [c3x_vecCap4Of_toNat hbound]
  rcases c3x_vecCap4Of_zero_or_ge4 n with h0 | h4
  · rw [h0]; rfl
  · have hne : vecCap4Of n ≠ 0 := by omega
    have hmax : max (2 * vecCap4Of n) 4 = 2 * vecCap4Of n := by omega
    simp only [hne, ↓reduceIte, hmax]

private theorem c3x_chainDoneEvents_succ {c : ChainG} {k : Nat} (hk : k < c.fields.length) :
    chainDoneEvents c (k + 1) =
      chainDoneEvents c k ++
        chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk) := by
  simp [chainDoneEvents, hk]

private theorem c3x_fitsEvents_step {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {c : ChainG} {k : Nat} (hk : k < c.fields.length)
    (hfit : FitsEvents M lim (M.stepEvents (chainDoneEvents c k) st) (chainRemEvents c k)) :
    FitsEvents M lim (M.stepEvents (chainDoneEvents c k) st)
      (chainFieldStepEvents (chainGAfter c k).keys.length (c.fields[k]'hk)) ∧
    FitsEvents M lim (M.stepEvents (chainDoneEvents c (k + 1)) st) (chainRemEvents c (k + 1)) := by
  rw [chainRemEvents_eq_cons hk, fitsEvents_append] at hfit
  rw [c3x_chainDoneEvents_succ hk, M.stepEvents_append]
  exact hfit

private theorem c3x_fitsEnv_dv2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hdv : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs hevs
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  subst hevs
  trivial

private theorem c3x_dv2_evs_eq_nil_of_some {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs : List AllocEvent} (hdv : decodeVarint bs = some p) (hevs : DecodeVarint2Env bs evs) :
    evs = [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hdv] at hevs
  exact hevs

private theorem c3x_chain3GAtCap_apply_srk (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) (b : List (BitVec 8)) :
    c3x_chain3GAtCap A_rep a capMk (c.apply (.srk b)) =
      chain3VecAt A_rep a b ∗ chain3VecAt A_rep (a + 0x18#64) c.priv ∗
        c3x_chainGRestCap A_rep a capMk c :=
  rfl

private theorem c3x_chain3GAtCap_apply_priv (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) (b : List (BitVec 8)) :
    c3x_chain3GAtCap A_rep a capMk (c.apply (.priv b)) =
      chain3VecAt A_rep a c.srk ∗ chain3VecAt A_rep (a + 0x18#64) b ∗
        c3x_chainGRestCap A_rep a capMk c :=
  rfl

private theorem c3x_chain3GAtCap_ck_none (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) (hck : c.ck = none) :
    c3x_chain3GAtCap A_rep a capMk c =
      chain3VecAt A_rep a c.srk ∗ chain3VecAt A_rep (a + 0x18#64) c.priv ∗
        ((∃∗ ptrMk : BitVec 64,
          vecAt A_rep 104 8 (fun mkg b => prostMsgKeyAt A_rep mkg b)
            (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
          (((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24)) := by
  unfold c3x_chain3GAtCap c3x_chainGRestCap
  rw [hck]

private theorem c3x_chain3GAtCap_apply_ck (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) (i : BitVec 32) (key : List (BitVec 8)) :
    c3x_chain3GAtCap A_rep a capMk (c.apply (.ck i key)) =
      chain3VecAt A_rep a c.srk ∗ chain3VecAt A_rep (a + 0x18#64) c.priv ∗
        ((∃∗ ptrMk : BitVec 64,
          vecAt A_rep 104 8 (fun mkg b => prostMsgKeyAt A_rep mkg b)
            (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
          (vecU8 A_rep (a + 0x48#64) key ∗ ((a + 0x60#64) ↦₃₂ i) ∗
            memRegion (a + 0x64#64) 4)) :=
  rfl

private def c3x_chainNoKeys (A_rep : RustAlloc) (a : BitVec 64) (c : ChainG) : SepProp :=
  chain3VecAt A_rep a c.srk ∗ chain3VecAt A_rep (a + 0x18#64) c.priv ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A_rep (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

private theorem c3x_chain3GAtCap_keys_split (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    c3x_chain3GAtCap A_rep a capMk c =
      (∃∗ ptrMk : BitVec 64,
        vecAt A_rep 104 8 (fun mkg b => prostMsgKeyAt A_rep mkg b)
          (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
        c3x_chainNoKeys A_rep a c := by
  unfold c3x_chain3GAtCap c3x_chainGRestCap c3x_chainNoKeys
  sep_ac_rfl

private theorem c3x_chain3GAtCap_apply_key (A_rep : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) (mkg : MessageKeyGenerator) :
    c3x_chain3GAtCap A_rep a capMk (c.apply (.key mkg)) =
      (∃∗ ptrMk : BitVec 64,
        vecAt A_rep 104 8 (fun m b => prostMsgKeyAt A_rep m b)
          (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk (c.keys ++ [mkg])) ∗
        c3x_chainNoKeys A_rep a c :=
  c3x_chain3GAtCap_keys_split A_rep a capMk (c.apply (.key mkg))

private theorem c3x_bm_call_zero_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v ptr0 bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 b.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((vecU8At A.repAlloc v 0#64 ptr0 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hlen_lt63 : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 63 := by omega
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_240_aligned_c3_cro halign
  let gbm : BytesMergeGhost :=
    ⟨.lengthDelimited, v, 0#64, ptr0, [], bufRef, slot, curPtr,
      [BitVec.ofNat 8 b.length] ++ b ++ rest⟩
  have hmB : mergeBytes gbm.wt gbm.bs = some (b, rest) :=
    mergeBytes_lt128_seedChain b rest hb
  have hevs_eq : bytesMergeEventsCore gbm.wt gbm.valCap gbm.bs = bytesMergeEvents 0 b.length :=
    c3x_bytesMergeEventsCore_zero_eq hmB
  have hfit_bm : FitsEnv M lim st_cur (BytesMergeEnv gbm) := by
    rintro _ rfl
    rwa [hevs_eq]
  intro R' hm hL
  have hm_call : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)).pre (gbm, st_cur) s ∗ (F ∗ R') := by
    refine intro_withLsCodeRoLoaded_c3 hcro ?_
    rw [stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)] at hm
    unfold bytesMerge3RawSpec; dsimp only [gbm]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen_lt63, bytesMergeCapOk_zero, hfit_bm⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  obtain ⟨sm, hst1,
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hm_post⟩ | ⟨_, hm_pan⟩ | ⟨_, _, hm_ex⟩ | ⟨_, hm_oom⟩, _⟩ :=
    (hC.bm).no_fault_before_outcome (gbm, st_cur) (F ∗ R') s hpc hrun hm_call hsp_aligned hL
  · rw [hlr] at hpcm
    rw [hsp] at hspm
    have hclm : LibsignalCodeLoaded lsmpl sm.mem := libsignalCodeLoaded_preserve_c3 hcl hst1
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec] at hm_post
    rw [hmB, hsp] at hm_post
    dsimp only [gbm] at hm_post
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_post
    rcases hm_post with ⟨cap', ptr', evs_bm, hm_post⟩
    have hm_pure : sm.mem ⊨
        ⌜sm.trace = s.trace⌝ ∗
        (⌜BytesMergeEnv gbm evs_bm⌝ ∗
          (⌜sm.readReg64 .x0 = 0#64⌝ ∗
            (⌜BytesMergeCapOk cap' rest.length⌝ ∗
              ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
                sliceCursorAfter slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) rest ∗
                A.pool lim (M.stepEvents evs_bm st_cur) sm ∗
                stackAt (sp0 - 240#64) bytesMerge3Stack ∗ F) ∗ R')))) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_post
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj,
      satisfies_pure_sepConj, satisfies_pure_sepConj] at hm_pure
    rcases hm_pure with ⟨htrm, hevs_bm, hx0m, _hcapOk, hm_rest⟩
    have hevs_bm_eq : evs_bm = bytesMergeEvents 0 b.length := hevs_bm.trans hevs_eq
    subst hevs_bm_eq
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    rw [show ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 by simp] at hcur
    rw [hcur, ← stackAt_c3Sub_eq_bytesMerge (sp0 - 240#64)] at hm_rest
    have hm_next : sm.mem ⊨
        ((vecU8At A.repAlloc v cap' ptr' b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F) ∗ R' :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_rest
    obtain ⟨sf, hst2, hout2⟩ :=
      hnext sm cap' ptr' hpcm hrunm hspm hclm (htrm.trans htr) hcsm hx0m
        R' hm_next (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout2⟩
  · dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec] at hm_pan
    exact False.elim (not_satisfies_false_sepConj hm_pan)
  · exact False.elim (not_satisfies_false_sepConj hm_ex)
  · exact False.elim (not_satisfies_false_sepConj hm_oom)

private theorem c3x_bm_call_srk_zero_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128) (hb_ne : b ≠ [])
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 b.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((chain3VecAt A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A.repAlloc v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine sepWPp_mono_pre_c3
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A.repAlloc v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3x_bm_call_zero_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hfit hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine sepWPp_mono_pre_c3 ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left (chain3VecAt_of_ne_nil A.repAlloc v cap' ptr' hb_ne))

private theorem c3x_bm_call_vec_zero_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 b.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8 A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((chain3VecAt A.repAlloc v [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine sepWPp_mono_pre_c3
    (sepConj_mono_left (sepConj_mono_left (chain3VecAt_nil_elim A.repAlloc v))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun ptr0 => ?_
  refine c3x_bm_call_zero_cro hC v ptr0 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hfit hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine sepWPp_mono_pre_c3 ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

private theorem c3x_bm_call_vec1_zero_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 b.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 514) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc) (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v) (hx2 : s.readReg64 .x2 = bufRef)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        ((vecU8 A.repAlloc v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 b.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((vecU8At A.repAlloc v 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  refine c3x_bm_call_zero_cro hC v 1#64 bufRef slot curPtr sp0 ret_pc b rest hb hlen_lt
    hfit hcro hpc hrun hsp halign hcl htr hlr hx0 hx1 hx2 ?_
  intro sm cap' ptr' hpcm hrunm hspm hclm htrm hcsm hx0m
  refine sepWPp_mono_pre_c3 ?_ (hnext sm hpcm hrunm hspm hclm htrm hcsm hx0m)
  exact sepConj_mono_left (sepConj_mono_left
    (Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))))

private abbrev c3x_StepAtW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost) (st : M.σ)
    (R : SepProp) (s0 s : State) (Q : State → Prop) : Prop :=
  SegStepG (lsProg_516 (Rust.withPanics ext))
    (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) (x, st) R s0 s Q

private theorem c3x_segStepG_keep_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {x : ChainMergeGenGhost} {st : M.σ} {R : SepProp}
    {s0 s : State} {Q : State → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : c3x_StepAtW M A lim ext x st R s0 s Q) :
    c3x_StepAtW M A lim ext x st R s0 s
      (fun s' => LibsignalCodeRoLoaded lsmpl s'.mem ∧ Q s') := by
  intro hL
  obtain ⟨sf, hst, hq | hpan⟩ := hstep hL
  · exact ⟨sf, hst, Or.inl ⟨hcro.of_keepsFrozen hst.keepsFrozen, hq⟩⟩
  · exact ⟨sf, hst, Or.inr hpan⟩

private def c3x_LoopAtW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (x : ChainMergeGenGhost) (st : M.σ)
    (R : SepProp) (s0 : State) (k : Nat) (s : State) : Prop :=
  s.pc = chain3PCPlacedAtW ext 0xa8#64 ∧ s.status = .Running ∧ s.trace = s0.trace ∧
    calleeSavedVRegs s = calleeSavedVRegs s0 ∧
    LibsignalCodeLoaded lsmpl s.mem ∧
    s.sp = s0.sp - 0xf0#64 ∧ s.spAligned = true ∧ s.readReg64 .x29 = s0.sp - 0x50#64 ∧
    s.readReg64 .x19 = x.bufRef ∧ s.readReg64 .x20 = x.a ∧
    s.readReg64 .x21 = BitVec.ofNat 64 x.tail.length ∧
    s.readReg64 .x22 = s0.sp - 0xe8#64 ∧ s.readReg64 .x23 = 1#64 ∧ s.readReg64 .x24 = 104#64 ∧
    s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
    s.readReg64 .x28 = s0.readReg64 .x28 ∧
    x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
    FitsEvents M lim (M.stepEvents (chainDoneEvents x.c k) st) (chainRemEvents x.c k) ∧
    (s.mem ⊨ c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of (chainGAfter x.c k).keys.length)
        (chainGAfter x.c k) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
      stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R)

private def c3x_LoopCroAtW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ext : LibsignalHooks)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp)
    (s0 : State) (k : Nat) (s : State) : Prop :=
  LibsignalCodeRoLoaded lsmpl s.mem ∧
    c3x_LoopAtW M A lim ext x st R s0 k s

private def c3x_RetAtW [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 sf : State) : Prop :=
  Returned s0 sf ∧ CallingConventionPreserved s0 sf ∧
    (sf.mem ⊨ (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)).post
      (x, st) s0 sf ∗ R)

private theorem c3x_entry_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State)
    (hpc : s0.pc = lsmpl.base 516) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)).pre (x, st) s0 ∗ R)
    (hal : s0.spAligned = true) :
    c3x_StepAtW M A lim ext x st R s0 s0 (c3x_LoopCroAtW M A lim ext x st R s0 0) := by
  obtain ⟨hcro0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  refine c3x_segStepG_keep_cro hcro0 ?_
  intro hL0
  rcases x with ⟨a, c, bufRef, slot, ptr, tail⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcro0.1
  dsimp only [c3x_chainMerge3ExactCapRawSpecW] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hcOk, hlen_lt, hfit⟩, hmem⟩
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := sp_sub_240_aligned_c3_cro hsp_align
  have hmem1 : s0.mem ⊨ stackAt s0.sp chainMerge3StackX ∗
      (c3x_chain3GAtCap A.repAlloc a 0 ChainG.empty ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (c.payload ++ tail) ∗ A.pool lim st s0 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨s1, hst1, ⟨hpc1, hrun1, P1, hm1, hsp1, htr1, hvm1, hvregs1, hlr1, hx0_1, hx19_1, hx20_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hent1⟩ | ⟨_, hoom1⟩⟩ :=
    (step_chain3Entry_pre_placed_vm (ext := ext) a bufRef s0.sp
      (post := fun sm Pm =>
        sm.sp = s0.sp - 240#64 ∧ sm.trace = s0.trace ∧ VmPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
        sm.readReg64 .lr = lsmpl.base 516 + 56#64 ∧
        sm.readReg64 .x0 = bufRef ∧ sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
        sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
        sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
        (Pm ⊢ stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      hpc hrun rfl hsp_align hx0 hx1 hx2
      (fun _ _ _ hsp' htr' hvm' hvregs' hlr' hx0' hx19' hx20' hx26' hx27' hx28' hx29' _ hent =>
        ⟨hsp', htr', hvm', hvregs', hlr', hx0', hx19', hx20', hx26', hx27', hx28', hx29',
          hent⟩)).elim hmem1 hL0
  rotate_left; · exact (not_satisfies_false_sepConj hoom1).elim
  have hm1' := Satisfies.mono (sepConj_mono_left hent1) hm1
  have hpool1 : A.pool lim st s0 = A.pool lim st s1 :=
    (congrArg CryptoVerification.RustHeap.RustAlloc.pool (A.atState_eq_of_vmPreserved lim st hvm1)).symm
  have hal1 : s1.spAligned = true := by simp only [State.spAligned, hsp1, beq_iff_eq]; exact hsp_sub_align
  have hdec : decodeVarint (c.payload ++ tail) = some (BitVec.ofNat 64 c.enc.length, c.enc ++ tail) := by
    rw [show c.payload ++ tail = encodeVarint (BitVec.ofNat 64 c.enc.length) ++ (c.enc ++ tail) by
      unfold ChainG.payload; rw [List.append_assoc]]
    exact decodeVarint_encodeVarint (BitVec.ofNat 64 c.enc.length) (c.enc ++ tail)
  let gvar : DecodeVarintSlowGhost := ⟨bufRef, slot, ptr, c.payload ++ tail⟩
  let F_call : SepProp :=
    memRegion (s0.sp - 240#64 - BitVec.ofNat 64 chainMerge3SubStackX)
        (chainMerge3SubStackX - CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX) ∗
      chain3SavedRegs s0.sp s0 ∗ c3x_chain3GAtCap A.repAlloc a 0 ChainG.empty
  have hlen63 : (c.payload ++ tail).length < 2 ^ 63 := Nat.lt_trans hlen_lt (by decide)
  have hfit_dv : FitsEnv M lim st (DecodeVarint2Env gvar.bs) := c3x_fitsEnv_dv2_of_some hdec
  have hm1_call : s1.mem ⊨ (withLsCl lsmpl (decodeVarint2SpecX A lim)).pre (gvar, st) s1 ∗ (F_call ∗ R) := by
    refine intro_withLsCl_c3 (libsignalCodeLoaded_preserve_c3 hcl0 hst1) ?_
    unfold decodeVarint2SpecX; dsimp only [gvar]
    rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hx0_1, hlen63, hfit_dv⟩, ?_⟩
    rw [stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64), hpool1] at hm1'
    rw [hsp1]; dsimp only [F_call]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1'
  obtain ⟨s2, hst2, ⟨⟨hpc2, _, hrun2⟩, ⟨hsp2, hcs2⟩, hm2⟩ | ⟨_, hm2_pan⟩ | ⟨_, _, hm2_ex⟩ | ⟨_, hm2_oom⟩, _⟩ :=
    (hC.dv).no_fault_before_outcome (gvar, st) (F_call ∗ R) s1 hpc1 hrun1 hm1_call hal1 (hst1.codeLoaded hL0)
  · have hpc2' : s2.pc = lsmpl.base 516 + 56#64 := by rw [hpc2, hlr1]
    have hsp2' : s2.sp = s0.sp - 240#64 := by rw [hsp2, hsp1]
    rcases hcs2 with ⟨hx19_c, hx20_c, _, _, _, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩
    have hx19_2 : s2.readReg64 .x19 = bufRef := hx19_c.trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = a := hx20_c.trans hx20_1
    have hx26_2 : s2.readReg64 .x26 = s0.readReg64 .x26 := hx26_c.trans hx26_1
    have hx27_2 : s2.readReg64 .x27 = s0.readReg64 .x27 := hx27_c.trans hx27_1
    have hx28_2 : s2.readReg64 .x28 = s0.readReg64 .x28 := hx28_c.trans hx28_1
    have hx29_2 : s2.readReg64 .x29 = s0.sp - 80#64 := hx29_c.trans hx29_1
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs_c.trans hvregs1
    obtain ⟨_, hm2⟩ := extract_withLsCl_post_c3 hm2
    unfold decodeVarint2SpecX at hm2; dsimp only [gvar] at hm2; rw [hdec] at hm2; dsimp only at hm2
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm2
    rcases hm2 with ⟨evs0, hm2⟩
    have hm2_pure : s2.mem ⊨
        ⌜(s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = BitVec.ofNat 64 c.enc.length) ∧
          s2.trace = s1.trace ∧ DecodeVarint2Env (c.payload ++ tail) evs0⌝ ∗
        ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st) s2 ∗
          stackAt s1.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
          sliceCursorAfter slot ptr (c.payload ++ tail) (c.enc ++ tail) ∗ F_call ∗ R) := by
      have h1 : s2.mem ⊨
          ⌜s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = BitVec.ofNat 64 c.enc.length⌝ ∗
          (⌜s2.trace = s1.trace⌝ ∗
            (⌜DecodeVarint2Env (c.payload ++ tail) evs0⌝ ∗
              ((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs0 st) s2 ∗
                stackAt s1.sp CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
                sliceCursorAfter slot ptr (c.payload ++ tail) (c.enc ++ tail) ∗ F_call ∗ R))) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
      rw [satisfies_pure_sepConj]
      exact ⟨⟨h1.1, h1.2.1, h1.2.2.1⟩, h1.2.2.2⟩
    rw [satisfies_pure_sepConj] at hm2_pure
    rcases hm2_pure with ⟨⟨⟨hx0_2, hx1_2⟩, htr2, hevs0⟩, hm2_rest⟩
    have hevs0_nil : evs0 = [] := c3x_dv2_evs_eq_nil_of_some hdec hevs0
    subst hevs0_nil
    rw [hsp1] at hm2_rest
    have hlenA : (c.enc ++ tail).length = c.enc.length + tail.length := List.length_append
    have hlt2 : c.enc.length + tail.length < 2 ^ 62 := by
      unfold ChainG.payload at hlen_lt; simp only [List.length_append] at hlen_lt; omega
    let p1 := ptr + BitVec.ofNat 64 ((c.payload ++ tail).length - (c.enc ++ tail).length)
    unfold sliceCursorAfter at hm2_rest
    have hm2_post : s2.mem ⊨
        ((bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))) ∗
        ((ptr ↦ₛ (c.payload ++ tail)) ∗ A.pool lim (M.stepEvents [] st) s2 ∗
          stackAt (s0.sp - 240#64) CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.decodeVarint2StackX ∗
          F_call ∗ R) := by
      rw [← hlenA]; dsimp only [p1]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_rest
    obtain ⟨s3, hst3, ⟨hpc3, hrun3, P3, hm3, hsp3, htr3, hvm3, hvregs3, hx19_3, hx20_3, hx21_3,
        hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3, hx29_3, hent3⟩ | ⟨_, hoom3⟩⟩ :=
      (step_chain3Entry_post_placed_vm (ext := ext) a bufRef slot p1 s0.sp
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) c.enc.length tail.length hlt2
        (post := fun sm Pm =>
          sm.sp = s0.sp - 240#64 ∧ sm.trace = s2.trace ∧ VmPreserved s2 sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s2 ∧
          sm.readReg64 .x19 = bufRef ∧ sm.readReg64 .x20 = a ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 tail.length ∧ sm.readReg64 .x22 = s0.sp - 232#64 ∧
          sm.readReg64 .x23 = 1#64 ∧ sm.readReg64 .x24 = 104#64 ∧
          sm.readReg64 .x26 = s0.readReg64 .x26 ∧ sm.readReg64 .x27 = s0.readReg64 .x27 ∧
          sm.readReg64 .x28 = s0.readReg64 .x28 ∧ sm.readReg64 .x29 = s0.sp - 80#64 ∧
          (Pm ⊢ (bufRef ↦₆₄ slot) ∗ (slot ↦₆₄ p1) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (c.enc.length + tail.length))))
        hpc2' hrun2 hsp2' hsp_align hx0_2 hx1_2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
        (fun _ _ _ hsp' htr' hvm' hvregs' hx19' hx20' hx21' hx22' hx23' hx24' hx26' hx27' hx28' hx29' _ hent =>
          ⟨hsp', htr', hvm', hvregs', hx19', hx20', hx21', hx22', hx23', hx24', hx26', hx27', hx28', hx29', hent⟩)).elim
        hm2_post ((hst1.trans hst2).codeLoaded hL0)
    rotate_left; · exact (not_satisfies_false_sepConj hoom3).elim
    have hm3' := Satisfies.mono (sepConj_mono_left hent3) hm3
    have hpool3 : A.pool lim (M.stepEvents [] st) s2 = A.pool lim (M.stepEvents [] st) s3 :=
      (congrArg CryptoVerification.RustHeap.RustAlloc.pool
        (A.atState_eq_of_vmPreserved lim (M.stepEvents [] st) hvm3)).symm
    have hst_all := (hst1.trans hst2).trans hst3
    have hfit0 : FitsEvents M lim (M.stepEvents (chainDoneEvents c 0) st) (chainRemEvents c 0) := by
      simpa [chainDoneEvents, chainRemEvents_zero] using hfit
    refine ⟨s3, hst_all, Or.inl ⟨hpc3, hrun3, (htr3.trans htr2).trans htr1,
      hvregs3.trans hvregs2, libsignalCodeLoaded_preserve_c3 hcl0 hst_all, hsp3,
      by simp only [State.spAligned, hsp3, beq_iff_eq]; exact hsp_sub_align,
      hx29_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, hx28_3,
      hcOk, hlen_lt, hfit0, ?_⟩⟩
    dsimp only
    rw [show chainGAfter c 0 = ChainG.empty from rfl,
      show vecCap4Of ChainG.empty.keys.length = 0 from rfl,
      show chainDoneEvents c 0 = [] from rfl,
      show (c.fields.drop 0).flatMap ChainField.enc = c.enc by
        rw [List.drop_zero, ← chainG_enc_eq_fields_local c]]
    unfold sliceCursorAfter
    rw [hlenA, stackAt_c3Sub_to_decodeVarint (s0.sp - 240#64)]
    dsimp only [F_call, p1] at hm3'; rw [hlenA, hpool3] at hm3'
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm3'
  · dsimp only [withLsCl, decodeVarint2SpecX] at hm2_pan
    exact False.elim (not_satisfies_false_sepConj hm2_pan)
  · exact False.elim (not_satisfies_false_sepConj hm2_ex)
  · exact False.elim (not_satisfies_false_sepConj hm2_oom)

private theorem c3x_exit_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 s : State)
    (hs : c3x_LoopAtW M A lim ext x st R s0 x.c.fields.length s) :
    c3x_StepAtW M A lim ext x st R s0 s (c3x_RetAtW M A lim x st R s0) := by
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcl, hsp, hal, _, hx19, _, hx21, _, _, _,
    hx26, hx27, hx28, _, _, _hfit, hmem⟩
  have hpc' : s.pc = lsmpl.base 516 + 0xa8#64 := hpc
  have hsp_sub_align : s.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hal
  have hdone_eq : chainDoneEvents x.c x.c.fields.length = chainMergeEvents x.c := rfl
  rw [chainGAfter_fields x.c, hdone_eq, List.drop_length, List.flatMap_nil, List.nil_append,
    sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail] at hmem
  let ptrEnd := x.ptr + BitVec.ofNat 64 x.c.payload.length
  have hmem' : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        chain3SavedRegs s0.sp s0) ∗
        (c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c ∗
          (x.ptr ↦ₛ x.c.payload) ∗
          A.pool lim (M.stepEvents (chainMergeEvents x.c) st) s)) ∗ R := by
    dsimp only [ptrEnd]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (s0.readReg64 .lr) s
      (((x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAt x.slot ptrEnd x.tail ∗
        stackAt (s0.sp - 0xf0#64) chainMerge3SubStackX ∗
        chain3SavedRegs s0.sp s0) ∗
        (c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c ∗
          (x.ptr ↦ₛ x.c.payload) ∗
          A.pool lim (M.stepEvents (chainMergeEvents x.c) st) s))
      (fun sf Pf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)).post (x, st) s0 sf))
      (fun _ _ => False) := by
    refine step_chain3Exit_placed x.bufRef x.slot ptrEnd s0.sp x.tail
      hpc' hrun hsp hsp_sub_align hcl htr hvregs rfl hx19 hx21 hx26 hx27 hx28 ?_
    intro sf hpcf hrunf hspf _hclf hvmf htrf hx0f hcsf
    refine SepWPp.done hpcf hrunf ⟨hspf, hcsf, ?_⟩
    have hpool_eq :
        A.pool lim (M.stepEvents (chainMergeEvents x.c) st) s =
          A.pool lim (M.stepEvents (chainMergeEvents x.c) st) sf :=
      (congrArg CryptoVerification.RustHeap.RustAlloc.pool
        (A.atState_eq_of_vmPreserved lim (M.stepEvents (chainMergeEvents x.c) st) hvmf)).symm
    dsimp only [withLsCodeRoLoaded, c3x_chainMerge3ExactCapRawSpecW]
    rw [pure_sepConj_of_true ⟨htrf, hx0f⟩,
      sliceCursorAfter_append_eq_seedChain x.slot x.ptr x.c.payload x.tail, hpool_eq]
    dsimp only [ptrEnd]
    exact Entails.of_eq (by sep_ac_rfl)
  intro hL
  obtain ⟨sf, hsteps, hex⟩ := hwp R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, hsp_f, hcs_f, hent_f⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem c3x_tag1_dispatch_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 192#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace) (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x0a#64) (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 514 → s3.status = .Running → s3.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s3.mem → VmPreserved s2 s3 → s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 496#64 →
      (s3.readReg64 .x0).setWidth 8 = 2#8 →
      s3.readReg64 .x1 = a → s3.readReg64 .x2 = bufRef →
      Chain3LoopRegsPreserved s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2 P Q Qp := by
  change s2.pc = (blkPl_516).base + 192#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x0a#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 18 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl3
  exact hnext _ (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [hsp, wp_norm, arm64_norm]) hcl3 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3x_tag1_ret_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 : BitVec 64) {ret : BitVec 64} {s_init s4 : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 496#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace) (hx0 : s4.readReg64 .x0 = 0#64)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 168#64 → s5.status = .Running → s5.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s5.mem → VmPreserved s4 s5 → s5.trace = s_init.trace →
      Chain3LoopRegsPreserved s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4 P Q Qp := by
  change s4.pc = (blkPl_516).base + 496#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 168#64)
  intro m_strip
  iterate 2 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s4 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl5
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl5 hvm (by simp only [htr, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3x_tag2_dispatch_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (a bufRef sp0 : BitVec 64)
    {ret : BitVec 64} {s_init s2 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s2.pc = lsmpl.base 516 + 192#64) (hrun : s2.status = .Running)
    (hsp : s2.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (htr : s2.trace = s_init.trace) (hx0 : s2.readReg64 .x0 = 0#64)
    (hx1 : s2.readReg64 .x1 = 0x12#64) (hx19 : s2.readReg64 .x19 = bufRef)
    (hx20 : s2.readReg64 .x20 = a)
    (hnext : ∀ (s3 : State),
      s3.pc = lsmpl.base 514 → s3.status = .Running → s3.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s3.mem → VmPreserved s2 s3 → s3.trace = s_init.trace →
      s3.readReg64 .lr = lsmpl.base 516 + 272#64 →
      (s3.readReg64 .x0).setWidth 8 = 2#8 →
      s3.readReg64 .x1 = a + 24#64 → s3.readReg64 .x2 = bufRef →
      Chain3LoopRegsPreserved s2 s3 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s3 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s2 P Q Qp := by
  change s2.pc = (blkPl_516).base + 192#64 at hpc
  have h0 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s2.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1
  have h19 : s2.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s2.readReg64 (Reg.gpr 20#5) = a := hx20
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 20 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s2 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl3
  exact hnext _ (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [hsp, wp_norm, arm64_norm]) hcl3 hvm (by simp only [htr, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3x_tag2_ret_vm [LibsignalPlacement] {ext : String → Option (State → State)}
    (sp0 : BitVec 64) {ret : BitVec 64} {s_init s4 : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s4.pc = lsmpl.base 516 + 272#64) (hrun : s4.status = .Running)
    (hsp : s4.sp = sp0 - 240#64) (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (htr : s4.trace = s_init.trace) (hx0 : s4.readReg64 .x0 = 0#64)
    (hnext : ∀ (s5 : State),
      s5.pc = lsmpl.base 516 + 168#64 → s5.status = .Running → s5.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl s5.mem → VmPreserved s4 s5 → s5.trace = s_init.trace →
      Chain3LoopRegsPreserved s4 s5 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s5 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s4 P Q Qp := by
  change s4.pc = (blkPl_516).base + 272#64 at hpc
  have h0 : s4.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 168#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 168#64)
  intro m_strip
  iterate 2 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s4 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl5
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) (by simp only [hsp, wp_norm, arm64_norm])
    hcl5 hvm (by simp only [htr, wp_norm, arm64_norm])
    ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm]⟩

private theorem c3x_step_tag1_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64) (srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128) (hsrk_ne : srk ≠ [])
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 srk.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc a srk ∗ (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 srk.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc a [] ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 496#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc a [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x0a#8 :: rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc a [] ∗ A.pool lim st_cur s0 ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3_outer_head_vm bufRef slot ptr sp0 (0x0a#8 :: rem1) tail.length hlen_gt hlen_cons_lt
      hpc hrun hsp hcl htr hx19 hx21 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x0a#8 :: rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc a [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x0a#64 0x0a#8 rem1
      (decodeVarint_0a_cons rem1) hlen_cons_lt hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine c3x_tag1_dispatch_vm a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.1.trans hx20) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3'
    refine SepWPp.done hpc3 hrun3
      ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs2.trans hregs3', ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3x_bm_call_srk_zero_cro hC a bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 496#64)
      srk (rest ++ tail) hsrk_lt hsrk_ne hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine c3x_tag1_ret_vm sp0 hpc4 hrun4 hsp4 hcl4 htr4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5'
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5'))
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents (bytesMergeEvents 0 srk.length) st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_step_tag2_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64) (priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128) (hpriv_ne : priv ≠ [])
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 priv.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 168#64) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef) (hx20 : s0.readReg64 .x20 = a)
    (hx21 : s0.readReg64 .x21 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      Chain3LoopRegsPreserved s0 sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 24#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 priv.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 24#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s_init.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 272#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = a + 24#64 ∧
      s3.readReg64 .x2 = bufRef ∧ Chain3LoopRegsPreserved s0 s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc (a + 24#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1) ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 24#64) [] ∗ A.pool lim st_cur s0 ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3_outer_head_vm bufRef slot ptr sp0 (0x12#8 :: rem1) tail.length hlen_gt hlen_cons_lt
      hpc hrun hsp hcl htr hx19 hx21 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 24#64) [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3a_dv_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 192#64) 0x12#64 0x12#8 rem1
      (decodeVarint_12_cons rem1) hlen_cons_lt hpc1 hrun1 hsp1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine c3x_tag2_dispatch_vm a bufRef sp0 hpc2 hrun2 hsp2 hcl2 htr2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.1.trans hx20) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hregs3'
    refine SepWPp.done hpc3 hrun3
      ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs2.trans hregs3', ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3x_bm_call_srk_zero_cro hC (a + 24#64) bufRef slot (ptr + 1#64) sp0 (lsmpl.base 516 + 272#64)
      priv (rest ++ tail) hpriv_lt hpriv_ne hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3 htr3
      hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    have hregs4 : Chain3LoopRegsPreserved s0 s4 := hregs3.trans (.of_calleeSaved hcs4)
    refine c3x_tag2_ret_vm sp0 hpc4 hrun4 hsp4 hcl4 htr4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5'
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5'))
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents (bytesMergeEvents 0 priv.length) st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_mem_fields_srk_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.srk b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem; rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h1

private theorem c3x_mem_fields_priv_ne_nil {c : ChainG} {b : List (BitVec 8)}
    (hmem : ChainField.priv b ∈ c.fields) : b ≠ [] := by
  unfold ChainG.fields at hmem; rcases c with ⟨srk, priv, ck, keys⟩
  by_cases h1 : srk = [] <;> by_cases h2 : priv = [] <;> cases ck <;>
    simp [h1, h2] at hmem <;> subst hmem <;> exact h2

private theorem c3x_srk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : c3x_LoopCroAtW M A lim ext x st R s0 k s) :
    c3x_StepAtW M A lim ext x st R s0 s (c3x_LoopCroAtW M A lim ext x st R s0 (k + 1)) := by
  rcases hs with ⟨hcro, hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen, hfit, hmem⟩
  refine c3x_segStepG_keep_cro hcro ?_
  intro hL
  obtain ⟨hfit_fld, hfit_next⟩ := c3x_fitsEvents_step hk hfit
  have hpc' : s.pc = lsmpl.base 516 + 168#64 := hpc
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_c3 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢; omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck _ _ => rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | key _ => rw [hfl_eq] at htag; simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := c3x_mem_fields_srk_ne_nil hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    have hfit_bm :
        FitsEvents M lim (M.stepEvents (chainDoneEvents x.c k) st) (bytesMergeEvents 0 b.length) := by
      rw [hfl_eq] at hfit_fld; exact hfit_fld
    let ck := chainGAfter x.c k
    let capMk := vecCap4Of ck.keys.length
    have hck_srk : ck.srk = [] := chainGAfter_srk_eq_nil hk hfl_eq
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) ck.priv ∗
        c3x_chainGRestCap A.repAlloc x.a capMk ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [c3x_chain3GAtCap, hck_srk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, capMk, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → c3x_LoopAtW M A lim ext x st R s0 (k + 1) sm)
        (fun _ _ => False) := by
      refine c3x_step_tag1_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hfit_bm hcro hpc' hrun hsp hsp0_align hcl htr
        hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hclm htrm hregsm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, hfit_next, ?_⟩
      have hkeys_eq : (chainGAfter x.c (k + 1)).keys = ck.keys := by
        rw [chainGAfter_succ hk, hfl_eq]; rfl
      have hdone_succ :
          M.stepEvents (bytesMergeEvents 0 b.length) (M.stepEvents (chainDoneEvents x.c k) st) =
            M.stepEvents (chainDoneEvents x.c (k + 1)) st := by
        rw [c3x_chainDoneEvents_succ hk, hfl_eq, M.stepEvents_append]; rfl
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            A.pool lim
              (M.stepEvents (bytesMergeEvents 0 b.length)
                (M.stepEvents (chainDoneEvents x.c k) st)) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of (chainGAfter x.c (k + 1)).keys.length)
              (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [hdone_succ, hkeys_eq, chainGAfter_succ hk, hfl_eq,
          c3x_chain3GAtCap_apply_srk A.repAlloc x.a capMk ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, capMk, F, rest]
        sep_ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact hpan.elim
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have hb_ne : b ≠ [] := c3x_mem_fields_priv_ne_nil hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]; exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by rwa [← henc]
    have hfit_bm :
        FitsEvents M lim (M.stepEvents (chainDoneEvents x.c k) st) (bytesMergeEvents 0 b.length) := by
      rw [hfl_eq] at hfit_fld; exact hfit_fld
    let ck := chainGAfter x.c k
    let capMk := vecCap4Of ck.keys.length
    have hck_priv : ck.priv = [] := chainGAfter_priv_eq_nil hk hfl_eq
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗ chain3VecAt A.repAlloc x.a ck.srk ∗
        c3x_chainGRestCap A.repAlloc x.a capMk ck ∗ chain3SavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) [] ∗
        sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) ∗ R := by
      rw [c3x_chain3GAtCap, hck_priv, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, capMk, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) [] ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F)
        (fun sm Pm => (sm.mem ⊨ Pm ∗ R) → c3x_LoopAtW M A lim ext x st R s0 (k + 1) sm)
        (fun _ _ => False) := by
      refine c3x_step_tag2_cro hC x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        b rest x.tail hb_lt hb_ne hlen_pb hfit_bm hcro hpc' hrun hsp hsp0_align hcl htr
        hx19 hx20 hx21 ?_
      intro sm hpcm hrunm hspm hclm htrm hregsm
      refine SepWPp.done hpcm hrunm fun hmem_m => ?_
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.2.2.trans hvregs, hclm, hspm,
        by simp only [State.spAligned, hspm, ← hsp]; exact hal,
        hregsm.2.2.2.2.2.2.2.2.2.1.trans hx29, hregsm.1.trans hx19, hregsm.2.1.trans hx20,
        hregsm.2.2.1.trans hx21, hregsm.2.2.2.1.trans hx22, hregsm.2.2.2.2.1.trans hx23,
        hregsm.2.2.2.2.2.1.trans hx24, hregsm.2.2.2.2.2.2.1.trans hx26,
        hregsm.2.2.2.2.2.2.2.1.trans hx27, hregsm.2.2.2.2.2.2.2.2.1.trans hx28,
        hcOk, hlen, hfit_next, ?_⟩
      have hkeys_eq : (chainGAfter x.c (k + 1)).keys = ck.keys := by
        rw [chainGAfter_succ hk, hfl_eq]; rfl
      have hdone_succ :
          M.stepEvents (bytesMergeEvents 0 b.length) (M.stepEvents (chainDoneEvents x.c k) st) =
            M.stepEvents (chainDoneEvents x.c (k + 1)) st := by
        rw [c3x_chainDoneEvents_succ hk, hfl_eq, M.stepEvents_append]; rfl
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 24#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            A.pool lim
              (M.stepEvents (bytesMergeEvents 0 b.length)
                (M.stepEvents (chainDoneEvents x.c k) st)) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗ F) =
          (c3x_chain3GAtCap A.repAlloc x.a (vecCap4Of (chainGAfter x.c (k + 1)).keys.length)
              (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st) sm ∗
            stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0) := by
        rw [hdone_succ, hkeys_eq, chainGAfter_succ hk, hfl_eq,
          c3x_chain3GAtCap_apply_priv A.repAlloc x.a capMk ck b, ← henc,
          ← curPtr_succ x.ptr hk, sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, capMk, F, rest]
        sep_ac_rfl
      rw [hpost_eq] at hmem_m; simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, ⟨_, _, _, hmf, hloop⟩ | ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩⟩ := hwp R hmem_pre hL
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact hpan.elim
    · exact (not_satisfies_false_sepConj hoom).elim

private theorem c3x_step_ck_ihead_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a slot ptr : BitVec 64) (outerTailLen : Nat) (b0 : BitVec 8)
    (rem1 afterCk : List (BitVec 8))
    (hlen_gt : afterCk.length < (b0 :: rem1).length) (hlen_lt : (b0 :: rem1).length < 2 ^ 62)
    {ret : BitVec 64} {s_init s : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x368#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 515 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x380#64 → s1.readReg64 .x0 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (b0 :: rem1)) ∗ F) Q Qp := by
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_lt
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x368#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 afterCk.length := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 515) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 515)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 6 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_step_k3c_dispatch_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x380#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx1 : s.readReg64 .x1 = 0x12#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 514 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      s1.readReg64 .lr = lsmpl.base 516 + 0x3bc#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 → s1.readReg64 .x1 = a + 0x48#64 →
      s1.readReg64 .x2 = bufRef →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x380#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h1 : s.readReg64 (Reg.gpr 1#5) = 0x12#64 := hx1
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 514) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 514)
  intro m_strip
  iterate 15 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]; rfl) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩

private theorem c3x_step_k3c_ret_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (sp0 bufRef a : BitVec 64) (outerTailLen innerTailLen : Nat)
    {ret : BitVec 64} {s_init s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 516 + 0x3bc#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0x368#64 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen innerTailLen s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1 P Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s P Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s.pc = (blkPl_516).base + 0x3bc#64 at hpc
  have h0 : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 innerTailLen := hx25
  have h26 : s.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0x368#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0x368#64)
  intro m_strip
  iterate 4 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  exact hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩

private theorem c3x_step_seg3d_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (a bufRef slot ptr sp0 : BitVec 64) (afterCk : List (BitVec 8)) (outerTailLen : Nat)
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = lsmpl.base 516 + 0x368#64)
    (hrun : s0.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (s1 : State),
      s1.pc = lsmpl.base 516 + 0xa8#64 → s1.status = .Running → LibsignalCodeLoaded lsmpl s1.mem →
      VmPreserved s0 s1 → s1.trace = s_init.trace → calleeSavedVRegs s1 = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s1 →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret s1
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr afterCk ∗
          stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr afterCk ∗
        stackAt (sp0 - 0xf0#64) chainMerge3SubStackX) ∗ F) Q Qp := by
  rcases hregs with ⟨hsp, hx29, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩
  change s0.pc = (blkPl_516).base + 0x368#64 at hpc
  have h29 : s0.readReg64 (Reg.gpr 29#5) = sp0 - 0x50#64 := hx29
  have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
  have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
  have h21 : s0.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 outerTailLen := hx21
  have h22 : s0.readReg64 (Reg.gpr 22#5) = sp0 - 0xe8#64 := hx22
  have h23 : s0.readReg64 (Reg.gpr 23#5) = 1#64 := hx23
  have h24 : s0.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s0.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 afterCk.length := hx25
  have h26 : s0.readReg64 (Reg.gpr 26#5) = s_init.readReg64 (Reg.gpr 26#5) := hx26
  have h27 : s0.readReg64 (Reg.gpr 27#5) = s_init.readReg64 (Reg.gpr 27#5) := hx27
  have h28 : s0.readReg64 (Reg.gpr 28#5) = s_init.readReg64 (Reg.gpr 28#5) := hx28
  refine SepWPp.of_sepWP_lscl_c3 (mid := lsmpl.base 516 + 0xa8#64) hcl ?_
  apply sepWP_seg_ls_vm (Q := lsProg_516 (hooksException (Rust.withPanics ext))) blkLib_eq_516
    (mid := lsmpl.base 516 + 0xa8#64)
  intro m_strip
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  iterate 7 wp_step
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro m_real hnsp
  have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) ?_
  intro hcl1
  refine sepWPp_mono_pre_c3 ?_ (hnext _ (by simp only [wp_norm, arm64_norm]; rfl)
    (by simp only [hrun, wp_norm, arm64_norm]) hcl1 hvm
    (by simp only [htr, wp_norm, arm64_norm]) (by simp only [hvregs, wp_norm, arm64_norm])
    ⟨by simp only [hsp, wp_norm, arm64_norm],
     by simp only [h29, wp_norm, arm64_norm],
     by simp only [h19, wp_norm, arm64_norm],
     by simp only [h20, wp_norm, arm64_norm],
     by simp only [h21, wp_norm, arm64_norm],
     by simp only [h22, wp_norm, arm64_norm],
     by simp only [h23, wp_norm, arm64_norm],
     by simp only [h24, wp_norm, arm64_norm],
     by simp only [h25, wp_norm, arm64_norm],
     by simp only [h26, wp_norm, arm64_norm],
     by simp only [h27, wp_norm, arm64_norm],
     by simp only [h28, wp_norm, arm64_norm]⟩)
  unfold sliceCursorAt
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_step_seg3c_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (key afterCk : List (BitVec 8)) (outerTailLen : Nat)
    (hk_lt : key.length < 128) (hlen_lt : (pbBytes 2 key ++ afterCk).length < 2 ^ 62)
    {st_cur : M.σ} {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 key.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hpc : s0.pc = lsmpl.base 516 + 872#64) (hrun : s0.status = .Running)
    (halign : sp0 &&& 15#64 = 0#64) (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace) (hvregs : calleeSavedVRegs s0 = calleeSavedVRegs s_init)
    (hregs : Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s0)
    (hnext : ∀ (sm : State),
      sm.pc = lsmpl.base 516 + 872#64 → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s_init.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s_init →
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A.repAlloc (a + 72#64) key ∗ (ptr ↦ₛ pbBytes 2 key) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 key).length) afterCk ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 key.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s0
      (((bufRef ↦₆₄ slot) ∗ chain3VecAt A.repAlloc (a + 72#64) [] ∗
        sliceCursorAt slot ptr (pbBytes 2 key ++ afterCk) ∗
        A.pool lim st_cur s0 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q Qp := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 key.length] ++ key ++ afterCk
  have hcons_eq : pbBytes 2 key ++ afterCk = 0x12#8 :: rem1 := by
    rw [pbBytes_lt128_eq_seedChain 2 (by decide) key hk_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : afterCk.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => LibsignalCodeLoaded lsmpl s3.mem ∧ s3.trace = s_init.trace ∧
      calleeSavedVRegs s3 = calleeSavedVRegs s_init ∧
      s3.readReg64 .lr = lsmpl.base 516 + 956#64 ∧ (s3.readReg64 .x0).setWidth 8 = 2#8 ∧
      s3.readReg64 .x1 = a + 72#64 ∧ s3.readReg64 .x2 = bufRef ∧
      Chain3InnerLoopRegs sp0 bufRef a outerTailLen afterCk.length s_init s3 ∧
      (P3 ⊢ (chain3VecAt A.repAlloc (a + 72#64) [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x12#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x12#8 :: rem1)) ∗
        (chain3VecAt A.repAlloc (a + 72#64) [] ∗ A.pool lim st_cur s0 ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3x_step_ck_ihead_vm sp0 bufRef a slot ptr outerTailLen 0x12#8 rem1
      afterCk hlen_gt hlen_cons_lt hpc hrun hcl htr hvregs hregs ?_
    intro s1 hpc1 hrun1 hcl1 hvm1 htr1 hvregs1 hlr1 hx0_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x12#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc (a + 72#64) [] ∗ F))
      (by
        rw [pool_eq_of_vm_c3 A lim st_cur hvm1, show (0x12#8 :: rem1) = [0x12#8] ++ rem1 from rfl]
        exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 896#64)
      0x12#64 [0x12#8] rem1 rfl hlen_cons_lt hpc1 hrun1 hregs1.1 halign hcl1 htr1 hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    obtain ⟨hregs2, hvregs2⟩ := c3ck_regs_after_call hregs1 hvregs1 hsp2 hcs2
    refine c3x_step_k3c_dispatch_vm sp0 bufRef a outerTailLen afterCk.length
      hpc2 hrun2 hcl2 htr2 hvregs2 hregs2 hx0_2 hx1_2 ?_
    intro s3 hpc3 hrun3 hcl3 hvm3 htr3 hvregs3 hlr3 hx0_3 hx1_3 hx2_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
      show BitVec.ofNat 64 ([0x12#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hcl3, htr3, hvregs3, hlr3, hx0_3, hx1_3, hx2_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 key.length] ++ key ++ afterCk).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3x_bm_call_vec_zero_cro hC (a + 72#64) bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 956#64) key afterCk hk_lt hrem1_lt hfit hcro3 hpc3 hrun3 hregs3.1
      halign hcl3 htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    obtain ⟨hregs4, hvregs4⟩ := c3ck_regs_after_call hregs3 hvregs3 hsp4 hcs4
    refine c3x_step_k3c_ret_vm sp0 bufRef a outerTailLen afterCk.length
      hpc4 hrun4 hcl4 htr4 hvregs4 hregs4 hx0_4 ?_
    intro s5 hpc5 hrun5 hcl5 hvm5 htr5 hvregs5 hregs5
    refine sepWPp_mono_pre_c3 ?_ (hnext s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5)
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents (bytesMergeEvents 0 key.length) st_cur) hvm5,
      pbBytes_ptr_advance_seedChain 2 (by decide) ptr key hk_lt,
      ← c3k3c_pointsTo_12_combine ptr key hk_lt]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_ck_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 3)
    (hs : c3x_LoopCroAtW M A lim ext x st R s0 k s) :
    c3x_StepAtW M A lim ext x st R s0 s (c3x_LoopCroAtW M A lim ext x st R s0 (k + 1)) := by
  rcases hs with ⟨hcro, hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hcOk, hlen_lt, hfit, hmem⟩
  refine c3x_segStepG_keep_cro hcro ?_
  intro hL
  obtain ⟨hfit_fld, hfit_next⟩ := c3x_fitsEvents_step hk hfit
  have hsp_sub_align : (s0.sp - 240#64) &&& 15#64 = 0#64 := by
    have : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    simpa [hsp] using this
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_240_aligned hsp_sub_align
  obtain ⟨⟨i, key, hck_some, hfl_eq⟩, hck_none⟩ := chainField_tag_three_info x.c k hk htag
  have hkey_len : key.length = 32 := hcOk.2.2.1 (i, key) hck_some
  have hkey_lt : key.length < 128 := by omega
  have hck_bounds := ckEnc_length_bounds_seedChain i hkey_len
  let b3b : List (BitVec 8) := pbVarint 1 i.toNat
  let b3c : List (BitVec 8) := pbBytes 2 key
  let ck_body : List (BitVec 8) := b3b ++ b3c
  have hck_lt : ck_body.length < 128 := by dsimp [ck_body, b3b, b3c]; omega
  let b3a : List (BitVec 8) := [0x1a#8, BitVec.ofNat 8 ck_body.length]
  let pfx : List (BitVec 8) := pfx_k x.c k
  let afterCk : List (BitVec 8) := rem_k x.c (k + 1) x.tail
  have hfl_enc : (x.c.fields[k]'hk).enc = b3a ++ (b3b ++ b3c) := by
    rw [hfl_eq]; exact chainField_ck_enc_eq i hkey_len
  have hfit_bm :
      FitsEvents M lim (M.stepEvents (chainDoneEvents x.c k) st) (bytesMergeEvents 0 key.length) := by
    rw [hfl_eq] at hfit_fld; exact hfit_fld
  have hrem_k : rem_k x.c k x.tail = 0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk) := by
    rw [rem_k_eq_cons x.c k x.tail hk, hfl_enc]; dsimp [b3a, ck_body]
  have hpay_eq : x.c.payload ++ x.tail = pfx ++ rem_k x.c k x.tail :=
    payload_append_eq_pfx_rem x.c k x.tail
  have houter_le : x.tail.length ≤ afterCk.length := by
    dsimp [afterCk, rem_k]; simp only [List.length_append]; omega
  have hlen_lt3a : 2 + (ck_body.length + afterCk.length) < 2 ^ 62 := by
    have h1 := hlen_lt; rw [hpay_eq, hrem_k] at h1
    simp only [List.length_append, List.length_cons] at h1; omega
  have hlen_lt3b : (b3b ++ b3c ++ afterCk).length < 2 ^ 62 := by
    have h1 : (b3b ++ b3c ++ afterCk).length = ck_body.length + afterCk.length := List.length_append
    omega
  have hlen_lt3c : (b3c ++ afterCk).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_lt3b ⊢; omega
  let c0 : ChainG := chainGAfter x.c k
  let capMk : Nat := vecCap4Of c0.keys.length
  let mkVecProp : SepProp :=
    ∃∗ ptrMk : BitVec 64,
      vecAt A.repAlloc 104 8 (fun mkg b => prostMsgKeyAt A.repAlloc mkg b)
        (x.a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c0.keys
  let ptr3a : BitVec 64 := x.ptr + BitVec.ofNat 64 pfx.length
  let ptr3b : BitVec 64 := ptr3a + 2#64
  let ptr3c : BitVec 64 := ptr3b + BitVec.ofNat 64 b3b.length
  let ptrEnd : BitVec 64 := ptr3c + BitVec.ofNat 64 b3c.length
  have hcur_init :
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) =
      (x.ptr ↦ₛ pfx) ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) := by
    change sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rem_k x.c k x.tail) = _
    rw [hpay_eq, sliceCursorAfter_append_eq_seedChain x.slot x.ptr pfx (rem_k x.c k x.tail), hrem_k]
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗
          mkVecProp ∗ (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)) ∗ R := by
    change s.mem ⊨ c3x_chain3GAtCap A.repAlloc x.a capMk c0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
        (((x.c.fields.drop k).flatMap ChainField.enc) ++ x.tail) ∗
      A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
      stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0 ∗ R at hmem
    rw [c3x_chain3GAtCap_ck_none A.repAlloc x.a capMk c0 hck_none, hcur_init] at hmem
    dsimp only [mkVecProp] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hfull : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 72#64) ↦₆₄ noneCap) ∗ memRegion (x.a + 80#64) 24 ∗
        sliceCursorAt x.slot ptr3a (0x1a#8 :: BitVec.ofNat 8 ck_body.length :: (ck_body ++ afterCk)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗
          mkVecProp ∗ (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0))
      (fun sf Pf =>
        LibsignalCodeLoaded lsmpl sf.mem ∧ sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 sf ∧
        (Pf ⊢ c3x_chain3GAtCap A.repAlloc x.a
            (vecCap4Of (chainGAfter x.c (k + 1)).keys.length) (chainGAfter x.c (k + 1)) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st) sf ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun _ _ => False) := by
    refine SepWPp.bind_lscro (mid := lsmpl.base 516 + 872#64)
      (Q1 := fun s5 P5 => LibsignalCodeLoaded lsmpl s5.mem ∧ s5.trace = s0.trace ∧
        calleeSavedVRegs s5 = calleeSavedVRegs s0 ∧
        Chain3InnerLoopRegs s0.sp x.bufRef x.a x.tail.length afterCk.length s0 s5 ∧
        (P5 ⊢ (((x.bufRef ↦₆₄ x.slot) ∗ chain3VecAt A.repAlloc (x.a + 72#64) [] ∗
          sliceCursorAt x.slot ptr3c (b3c ++ afterCk) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s5 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗
            mkVecProp ∗ (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))) hcro ?_ ?_
    · refine step_seg3a_cro hC x.a x.bufRef x.slot ptr3a s0.sp ck_body afterCk x.tail.length
        hck_lt houter_le hlen_lt3a hpc hrun hsp hsp0_align hcl htr hvregs
        hx29 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 ?_
      intro s4 hpc4 hrun4 hcl4 htr4 hvregs4 hregs4
      refine sepWPp_mono_pre_c3
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ ((x.a + 96#64) ↦₃₂ 0#32) ∗
          sliceCursorAt x.slot ptr3b (b3b ++ (b3c ++ afterCk)) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s4 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ chain3VecAt A.repAlloc (x.a + 72#64) [] ∗ memRegion (x.a + 100#64) 4 ∗
            chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗
            mkVecProp ∗ (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by
          have hck_eq : ck_body ++ afterCk = b3b ++ (b3c ++ afterCk) := by
            simp [ck_body, b3b, b3c, List.append_assoc]
          dsimp only [ptr3b, b3a]; rw [hck_eq]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine step_seg3b_cro hC x.a x.bufRef x.slot ptr3b s0.sp i b3c afterCk x.tail.length
        hlen_lt3b hpc4 hrun4 hsp0_align hcl4 htr4 hvregs4 hregs4 ?_
      intro s5 hpc5 hrun5 hcl5 htr5 hvregs5 hregs5
      refine SepWPp.done hpc5 hrun5 ⟨hcl5, htr5, hvregs5, hregs5, ?_⟩
      dsimp only [ptr3c, b3b]; exact Entails.of_eq (by sep_ac_rfl)
    · intro s5 P5 hpc5 hrun5 hcro5 ⟨hcl5, htr5, hvregs5, hregs5, hent5⟩
      refine sepWPp_mono_pre_c3 hent5 ?_
      refine c3x_step_seg3c_cro hC x.a x.bufRef x.slot ptr3c s0.sp key afterCk x.tail.length
        hkey_lt hlen_lt3c hfit_bm hcro5 hpc5 hrun5 hsp0_align hcl5 htr5 hvregs5 hregs5 ?_
      intro s6 hpc6 hrun6 hcl6 htr6 hvregs6 hregs6
      refine sepWPp_mono_pre_c3
        (P' := (((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrEnd afterCk ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          ((ptr3a ↦ₛ b3a) ∗ (ptr3b ↦ₛ b3b) ∗ (ptr3c ↦ₛ b3c) ∗ vecU8 A.repAlloc (x.a + 72#64) key ∗
            ((x.a + 96#64) ↦₃₂ i) ∗ memRegion (x.a + 100#64) 4 ∗ chain3VecAt A.repAlloc x.a c0.srk ∗
            chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗ mkVecProp ∗
            A.pool lim
              (M.stepEvents (bytesMergeEvents 0 key.length)
                (M.stepEvents (chainDoneEvents x.c k) st)) s6 ∗
            (x.ptr ↦ₛ pfx) ∗ chain3SavedRegs s0.sp s0)))
        (by dsimp only [ptrEnd, b3c]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine c3x_step_seg3d_vm x.a x.bufRef x.slot ptrEnd s0.sp afterCk x.tail.length
        hpc6 hrun6 hcl6 htr6 hvregs6 hregs6 ?_
      intro sf hpcf hrunf hclf hvmf htrf hvregsf hregsf
      refine SepWPp.done hpcf hrunf ⟨hclf, htrf, hvregsf, hregsf, ?_⟩
      have hc_succ : chainGAfter x.c (k + 1) = c0.apply (ChainField.ck i key) := by
        rw [chainGAfter_succ hk, hfl_eq]
      have hkeys_eq : (chainGAfter x.c (k + 1)).keys = c0.keys := by
        rw [hc_succ]; rfl
      have hdone_succ :
          M.stepEvents (bytesMergeEvents 0 key.length) (M.stepEvents (chainDoneEvents x.c k) st) =
            M.stepEvents (chainDoneEvents x.c (k + 1)) st := by
        rw [c3x_chainDoneEvents_succ hk, hfl_eq, M.stepEvents_append]; rfl
      rw [hkeys_eq, hc_succ, c3x_chain3GAtCap_apply_ck A.repAlloc x.a capMk c0 i key,
        pool_eq_of_vm_c3 A lim
          (M.stepEvents (bytesMergeEvents 0 key.length)
            (M.stepEvents (chainDoneEvents x.c k) st)) hvmf,
        hdone_succ]
      have hcur_end := combine_tag3_cursor x.slot x.ptr pfx b3a b3b b3c afterCk rfl
      dsimp only at hcur_end
      have htotal_end : (pfx ++ (b3a ++ (b3b ++ b3c))) ++ afterCk = x.c.payload ++ x.tail := by
        rw [← hfl_enc, ← pfx_k_succ x.c k hk]
        exact (payload_append_eq_pfx_rem x.c (k + 1) x.tail).symm
      rw [htotal_end] at hcur_end
      dsimp only [afterCk, rem_k] at hcur_end
      dsimp only [capMk, mkVecProp, afterCk, rem_k]
      change _ ⊢ (chain3VecAt A.repAlloc x.a c0.srk ∗ chain3VecAt A.repAlloc (x.a + 0x18#64) c0.priv ∗
          ((∃∗ ptrMk : BitVec 64,
            vecAt A.repAlloc 104 8 (fun mkg b => prostMsgKeyAt A.repAlloc mkg b)
              (x.a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of c0.keys.length)) ptrMk c0.keys) ∗
            (vecU8 A.repAlloc (x.a + 0x48#64) key ∗ ((x.a + 0x60#64) ↦₃₂ i) ∗
              memRegion (x.a + 0x64#64) 4))) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
          (((x.c.fields.drop (k + 1)).flatMap ChainField.enc) ++ x.tail) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st) sf ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0
      rw [← hcur_end]
      dsimp only [ptr3a, ptr3b, ptr3c, ptrEnd, afterCk, rem_k]
      exact Entails.of_eq (by sep_ac_rfl)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem_init hL
  rcases hex with ⟨hpcf, hrunf, Pf, hmf, hclf, htrf, hvregsf, hregsf, hentf⟩ |
    ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · rcases hregsf with ⟨hspf, hx29f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, _, hx26f, hx27f, hx28f⟩
    have half : sf.spAligned = true := by rw [State.spAligned, hspf, ← hsp]; exact hal
    have hmemf := Satisfies.mono (sepConj_mono_left hentf) hmf
    simp only [sepConj_assoc] at hmemf
    exact ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, htrf, hvregsf, hclf, hspf, half, hx29f, hx19f, hx20f,
      hx21f, hx22f, hx23f, hx24f, hx26f, hx27f, hx28f, hcOk, hlen_lt, hfit_next, hmemf⟩⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem c3x_step_mkSeed_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (bufRef slot ptr sp0 : BitVec 64) (seed rest : List (BitVec 8))
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hseed_lt : seed.length < 128) (hlen_lt : (pbBytes 5 seed ++ rest).length < 2 ^ 62)
    (hfit : FitsEvents M lim st_cur (bytesMergeEvents 0 seed.length))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx22 : s.readReg64 .x22 = sp0 - 232#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 580#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace →
      sm.readReg64 .x25 = BitVec.ofNat 64 rest.length → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ vecU8 A.repAlloc (sp0 - 160#64) seed ∗ (ptr ↦ₛ pbBytes 5 seed) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 5 seed).length) rest ∗
          A.pool lim (M.stepEvents (bytesMergeEvents 0 seed.length) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗
        sliceCursorAt slot ptr (pbBytes 5 seed ++ rest) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 seed.length] ++ seed ++ rest
  have hcons_eq : pbBytes 5 seed ++ rest = 0x2a#8 :: rem1 := by
    rw [CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_lt128_eq_seedChain
      5 (by decide) seed hseed_lt]
    simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : rest.length < (0x2a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x2a#8 :: rem1).length < 2 ^ 62 := by rw [← hcons_eq]; exact hlen_lt
  dsimp only [chain3PCPlacedAtW] at hpc hnext
  refine SepWPp.bind_lscro (mid := lsmpl.base 514)
    (Q1 := fun s3 P3 => s3.sp = sp0 - 240#64 ∧ LibsignalCodeLoaded lsmpl s3.mem ∧
      s3.trace = s0.trace ∧ s3.readReg64 .lr = lsmpl.base 516 + 680#64 ∧
      (s3.readReg64 .x0).setWidth 8 = 2#8 ∧ s3.readReg64 .x1 = sp0 - 160#64 ∧
      s3.readReg64 .x2 = bufRef ∧ s3.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧
      Chain3MkRegs s s3 ∧
      (P3 ⊢ (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot (ptr + 1#64) rem1 ∗
        A.pool lim st_cur s3 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ ((ptr ↦ₛ [0x2a#8]) ∗ F))) hcro ?_ ?_
  · rw [hcons_eq]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr (0x2a#8 :: rem1)) ∗
        (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ A.pool lim st_cur s ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine step_c3ihead_placed_vm bufRef slot ptr 0x2a#8 rem1 rest
      hlen_gt hlen_cons_lt hpc hrun hcl hx19 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hx25_1 hregs1
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr ([0x2a#8] ++ rem1) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        (vecU8At A.repAlloc (sp0 - 160#64) 0#64 1#64 [] ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3_dv_call_cro hC bufRef slot ptr sp0 (lsmpl.base 516 + 604#64)
      0x2a#64 [0x2a#8] rem1 rfl hlen_cons_lt hpc1 hrun1 (hsp1.trans hsp) halign hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_
    intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hcs2 hx0_2 hx1_2
    have hregs2 : Chain3MkRegs s s2 := hregs1.trans (.of_calleeSaved hcs2)
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs2.2.2.2.2.2.2.1.trans hx25_1
    refine step_c3seed_key_placed_vm bufRef sp0 hpc2 hrun2 hcl2 hx0_2 hx1_2
      (hregs2.1.trans hx19) (hregs2.2.2.2.1.trans hx22) ?_
    intro s3 hpc3 hrun3 hsp3 hcl3 hvm3 htr3 hlr3 hx0_3 hx1_3 hx2_3 hx25_3 hregs3
    refine SepWPp.done hpc3 hrun3 ⟨hsp3.trans hsp2, hcl3, htr3.trans htr2, hlr3,
      hx0_3, hx1_3, hx2_3, hx25_3.trans hx25_2, hregs2.trans hregs3, ?_⟩
    rw [pool_eq_of_vm_c3 A lim st_cur hvm3,
      show BitVec.ofNat 64 ([0x2a#8] : List (BitVec 8)).length = 1#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)
  · intro s3 P3 hpc3 hrun3 hcro3 ⟨hsp3, hcl3, htr3, hlr3, hx0_3, hx1_3, hx2_3, hx25_3, hregs3, hent3⟩
    refine sepWPp_mono_pre_c3 hent3 ?_
    have hrem1_lt : ([BitVec.ofNat 8 seed.length] ++ seed ++ rest).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine c3x_bm_call_vec1_zero_cro hC (sp0 - 160#64) bufRef slot (ptr + 1#64) sp0
      (lsmpl.base 516 + 680#64) seed rest hseed_lt hrem1_lt hfit hcro3 hpc3 hrun3 hsp3 halign hcl3
      htr3 hlr3 hx0_3 hx1_3 hx2_3 ?_
    intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hcs4 hx0_4
    have hregs4 : Chain3MkRegs s s4 := hregs3.trans (.of_calleeSaved hcs4)
    have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 rest.length :=
      hcs4.2.2.2.2.2.2.1.trans hx25_3
    refine step_c3seed_icont_placed_vm hpc4 hrun4 hcl4 hx0_4 ?_
    intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hx25_5 hregs5
    refine sepWPp_mono_pre_c3 ?_
      (hnext s5 hpc5 hrun5 (hsp5.trans hsp4) hcl5 (htr5.trans htr4)
        (hx25_5.trans hx25_4) (hregs4.trans hregs5))
    rw [pool_eq_of_vm_c3 A lim (M.stepEvents (bytesMergeEvents 0 seed.length) st_cur) hvm5,
      CryptoVerification.E2E.Record.DeserializeSeed.pbBytes_ptr_advance_seedChain
        5 (by decide) ptr seed hseed_lt, ← c3seed_pointsTo_2a_combine ptr seed hseed_lt]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_stackAt_c3Sub_to_growOne (sp : BitVec 64) :
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

private theorem c3x_vecAt_keys_open (A_rep : RustAlloc) (a cap : BitVec 64)
    (keys : List MessageKeyGenerator) :
    (∃∗ ptr : BitVec 64,
      vecAt A_rep 104 8 (fun mkg b => prostMsgKeyAt A_rep mkg b) (a + 0x30#64) cap ptr keys) ⊢
      ∃∗ ptr : BitVec 64,
        ⌜keys.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        (if cap = 0#64 then emp
         else A_rep.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun mkg b => prostMsgKeyAt A_rep mkg b) 104 ptr keys ∗
           memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) := by
  unfold vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e38, e40, h0]
  by_cases hcap : cap = 0#64 <;> simp only [hcap, ↓reduceIte] <;> exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_vecBuf_keys_full_open (A_rep : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hfull : keys.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A_rep.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun mkg b => prostMsgKeyAt A_rep mkg b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢
            arrayAt (fun mkg b' => prostMsgKeyAt A_rep mkg b') 104 b keys⌝ ∗
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
    rw [← hbs_cap]; exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by sep_ac_rfl))

private theorem c3x_vecBuf_keys_not_full_open (A_rep : RustAlloc) (cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (hlt : keys.length + 1 ≤ cap.toNat)
    (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A_rep.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun mkg b => prostMsgKeyAt A_rep mkg b) 104 ptr keys ∗
       memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) ((cap.toNat - keys.length) * 104)) =
      (A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun mkg b => prostMsgKeyAt A_rep mkg b) 104 ptr keys ∗
        memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap.toNat - (keys.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hlt
  have hmr := memRegion_spare_split_of_lt cap ptr keys.length hlt hcap_lt
  simp only [hcap0, ↓reduceIte] at hmr ⊢
  rw [hmr]

private theorem c3x_vecAt_keys_push_fold (A_rep : RustAlloc) (a cap ptr : BitVec 64)
    (keys : List MessageKeyGenerator) (mkg : MessageKeyGenerator)
    (hcap_le : keys.length + 1 ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
      A_rep.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
      prostMsgKeyAt A_rep mkg (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap.toNat - (keys.length + 1)) * 104) ⊢
    ∃∗ ptr' : BitVec 64,
      vecAt A_rep 104 8 (fun m b => prostMsgKeyAt A_rep m b) (a + 0x30#64) cap ptr'
        (keys ++ [mkg]) := by
  have hne0 : cap ≠ 0#64 := by intro h0; subst h0; simp at hcap_le
  have hlen : (keys ++ [mkg]).length = keys.length + 1 := by simp
  unfold vecAt vecHeader vecBuf
  refine Entails.sepExists_right ptr ?_
  have e38 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have e40 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hif : (if cap = 0 then emp else A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr (keys ++ [mkg]) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys ++ [mkg]).length * 104))
          ((cap.toNat - (keys ++ [mkg]).length) * 104)) =
      A_rep.live ptr (cap.toNat * 104) 8 ∗
      (arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
        prostMsgKeyAt A_rep mkg (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
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
            prostMsgKeyAt A_rep mkg (ptr + BitVec.ofNat 64 (keys.length * 104))) ∗
          memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
            ((cap.toNat - (keys.length + 1)) * 104))) =
      ⌜keys.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 (keys.length + 1)) ∗
        A_rep.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr keys ∗
        prostMsgKeyAt A_rep mkg (ptr + BitVec.ofNat 64 (keys.length * 104)) ∗
        memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap.toNat - (keys.length + 1)) * 104)) := by sep_ac_rfl
  rw [hgrp]; exact Entails.pure_right ⟨hcap_le, hcap_lt, hptr⟩ (Entails.refl _)

private theorem c3x_grow_call_cro [LibsignalPlacement] {M : AllocCostModel}
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
      cap' = BitVec.ofNat 64 (max (2 * cap.toNat) 4) →
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
    rw [c3x_stackAt_c3Sub_to_growOne (sp0 - 240#64)] at hm
    unfold growOneChainSpecX growOne104SpecX
    dsimp only
    have h0 : (0 : BitVec 64) = 0#64 := rfl
    rw [e38, h0, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hbs_cap, hptr, hmax_le, hfit⟩, ?_⟩
    dsimp only [F_grow]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
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
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_post
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
      rw [c3x_stackAt_c3Sub_to_growOne (sp0 - 240#64)]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_rest
    obtain ⟨sf, hst2, hout2⟩ :=
      hnext sm cap' ptr' rfl hcap'_le hcap'_lt hptr' hpcm hrunm hspm hclm
        (htrm.trans htr) hcsm R' hm_next (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hout2⟩
  · dsimp only [withLsCl, growOneChainSpecX, growOne104SpecX] at hm_pan
    exact False.elim (not_satisfies_false_sepConj hm_pan)
  · exact False.elim (not_satisfies_false_sepConj hm_ex)
  · exact False.elim (not_satisfies_false_sepConj hm_oom)

private theorem c3x_push4d_full_vm [LibsignalPlacement]
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
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_push4d_notfull_vm [LibsignalPlacement]
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
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_push4d_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64)
    (keys : List MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {st_cur : M.σ} {ret : BitVec 64} {s0 s : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur
      (if keys.length < vecCap4Of keys.length then [] else vec104GrowEvents (vecCap4Of keys.length)))
    (hpc : s.pc = lsmpl.base 516 + 0x244#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp0 - 240#64) (hsp_align : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      let cap' : BitVec 64 := BitVec.ofNat 64 (vecCap4Of (keys.length + 1))
      keys.length + 1 ≤ cap'.toNat → cap'.toNat * 104 < 2 ^ 63 → ptr' ≠ 0#64 →
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
          A.pool lim
            (M.stepEvents
              (if keys.length < vecCap4Of keys.length then []
               else vec104GrowEvents (vecCap4Of keys.length)) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b)
            (a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of keys.length)) ptrMk keys) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  let cap : BitVec 64 := BitVec.ofNat 64 (vecCap4Of keys.length)
  have hcap_nat : cap.toNat = vecCap4Of keys.length := c3x_vecCap4Of_toNat hbound
  apply SepWPp.fold (c3x_vecAt_keys_open A.repAlloc a cap keys) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hcap_le, hcap_lt, hptr⟩
  by_cases hfull : keys.length = cap.toNat
  · have hnlt : ¬ keys.length < vecCap4Of keys.length := by omega
    have hevs_eq :
        (if keys.length < vecCap4Of keys.length then []
         else vec104GrowEvents (vecCap4Of keys.length)) = growOne104Events cap := by
      simp only [hnlt, ↓reduceIte, cap]; exact (c3x_growOne104Events_eq hbound).symm
    have hfit_grow : FitsEnv M lim st_cur (GrowOne104Env cap) := by
      rintro _ rfl; rwa [← hevs_eq]
    have hcap_succ :
        BitVec.ofNat 64 (max (2 * cap.toNat) 4) =
          BitVec.ofNat 64 (vecCap4Of (keys.length + 1)) := by
      congr 1
      rw [vecCap4Of_succ]
      unfold vecCap4Push
      simp only [hnlt, ↓reduceIte, hcap_nat, c3x_max_eq_vecCap4Next]
    apply SepWPp.fold (c3x_vecBuf_keys_full_open A.repAlloc cap ptr keys hfull) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bs; apply SepWPp.exists_elim; intro H
    apply SepWPp.pure_left; rintro ⟨hbs_cap, hmov⟩
    have hbs_len : bs.length = keys.length * 104 := by rw [hbs_cap, hfull]
    refine sepWPp_mono_pre_c3
      (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length)) ∗
        ((if cap = 0#64 then emp else (A.repAlloc).live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H ∗
          A.pool lim st_cur s ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3x_push4d_full_vm a bufRef slot ptr_rest cap ptr keys rest hfull
      hpc hrun hcl hx19 hx20 hx24 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hlr1 hx0_1 hx25_1 hregs1
    have hsp_align1 : s1.spAligned = true := spAligned_of_sp_eq hsp1 hsp_align
    refine sepWPp_mono_pre_c3
      (P' := (((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp else (A.repAlloc).live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
        A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
        ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗ H ∗ F))
      (by rw [pool_eq_of_vm_c3 A lim st_cur hvm1]; exact Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3x_grow_call_cro hC a cap ptr sp0 (lsmpl.base 516 + 0x178#64) bs keys.length
      hfull hbs_len hptr hbound hfit_grow hpc1 hrun1 (hsp1.trans hsp) hsp_align1 hcl1
      (htr1.trans htr) hlr1 hx0_1 ?_
    intro sm cap' ptr' hcap'_eq hcap'_le hcap'_lt hptr' hpcm hrunm hspm hclm htrm hcsm
    have hcap'_succ : cap' = BitVec.ofNat 64 (vecCap4Of (keys.length + 1)) :=
      hcap'_eq.trans hcap_succ
    subst hcap'_succ
    have hregs_m : Chain3MkRegs s sm := hregs1.trans (.of_calleeSaved hcsm)
    have hx25_m : sm.readReg64 .x25 = BitVec.ofNat 64 keys.length := by
      rw [hcsm.2.2.2.2.2.2.1, hx25_1, hfull, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hsp_align_m : sm.spAligned = true := spAligned_of_sp_eq (hspm.trans hsp.symm) hsp_align
    apply SepWPp.fold (hmov ptr') (by sep_frame)
    refine sepWPp_mono_pre_c3 ?_ (hnext sm ptr' hcap'_le hcap'_lt hptr' hpcm hrunm hspm
      hsp_align_m hclm htrm hregs_m (hregs_m.2.1.trans hx20) (hregs_m.2.2.2.2.2.1.trans hx24) hx25_m)
    rw [← hevs_eq]
    dsimp only [RustCliAllocBudget.repAlloc]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hcap_le' : keys.length + 1 ≤ cap.toNat := by omega
    have hlt : keys.length < vecCap4Of keys.length := by omega
    have hevs_eq :
        (if keys.length < vecCap4Of keys.length then []
         else vec104GrowEvents (vecCap4Of keys.length)) = [] := by
      simp [hlt]
    have hcap_succ : cap = BitVec.ofNat 64 (vecCap4Of (keys.length + 1)) := by
      dsimp only [cap]; congr 1; rw [vecCap4Of_succ]; unfold vecCap4Push; simp [hlt]
    rw [c3x_vecBuf_keys_not_full_open A.repAlloc cap ptr keys hcap_le' hcap_lt]
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
      (Entails.of_eq (by sep_ac_rfl)) ?_
    refine c3x_push4d_notfull_vm a bufRef slot ptr_rest cap ptr keys rest
      hcap_le hfull hpc hrun hcl hx19 hx20 hx24 hx25 ?_
    intro s1 hpc1 hrun1 hsp1 hcl1 hvm1 htr1 hx20_1 hx24_1 hx25_1 hregs1
    have hsp_align1 : s1.spAligned = true := spAligned_of_sp_eq hsp1 hsp_align
    have hcap_le_succ : keys.length + 1 ≤ (BitVec.ofNat 64 (vecCap4Of (keys.length + 1))).toNat := by
      rwa [← hcap_succ]
    have hcap_lt_succ : (BitVec.ofNat 64 (vecCap4Of (keys.length + 1))).toNat * 104 < 2 ^ 63 := by
      rwa [← hcap_succ]
    refine sepWPp_mono_pre_c3 ?_ (hnext s1 ptr hcap_le_succ hcap_lt_succ hptr
      hpc1 hrun1 (hsp1.trans hsp) hsp_align1 hcl1 (htr1.trans htr)
      hregs1 hx20_1 hx24_1 hx25_1)
    rw [pool_eq_of_vm_c3 A lim st_cur hvm1, hevs_eq, ← hcap_succ]
    change _ ⊢ (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
      ((a + 0x30#64) ↦₆₄ cap) ∗ ((a + 0x38#64) ↦₆₄ ptr) ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (A.repAlloc).live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr keys ∗
      memRegion (ptr + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
      memRegion (ptr + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap.toNat - (keys.length + 1)) * 104) ∗
      A.pool lim st_cur s1 ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
    exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_push4e_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (A_rep : RustAlloc) (a cap' ptr' sp0 : BitVec 64)
    (keys : List MessageKeyGenerator) (mkg : MessageKeyGenerator)
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
        (((∃∗ ptrMk : BitVec 64,
          vecAt A_rep 104 8 (fun m b => prostMsgKeyAt A_rep m b) (a + 0x30#64) cap' ptrMk
            (keys ++ [mkg])) ∗
          memRegion (sp0 - 0xe8#64) 104) ∗ F) Q Qp) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      ((((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
        ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
        A_rep.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun m b => prostMsgKeyAt A_rep m b) 104 ptr' keys ∗
        memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
        memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
          ((cap'.toNat - (keys.length + 1)) * 104) ∗
        prostMsgKeyAt A_rep mkg (sp0 - 0xe8#64)) ∗ F) Q Qp := by
  have hsp_align_bv : s.sp &&& 15#64 = 0#64 := eq_of_beq hsp_align
  have hmadd := ptr_madd_104_eq ptr' keys.length
  have hadd1 := ofNat_add_one_eq keys.length
  change s.pc = (blkPl_516).base + 0x178#64 at hpc
  have h20 : s.readReg64 (Reg.gpr 20#5) = a := hx20
  have h24 : s.readReg64 (Reg.gpr 24#5) = 104#64 := hx24
  have h25 : s.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 keys.length := hx25
  apply SepWPp.fold (prostMsgKeyAt_move_chunks104 A_rep (sp0 - 0xe8#64) mkg) (by sep_frame)
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
    (c3x_vecAt_keys_push_fold A_rep a cap' ptr' keys mkg hcap_le hcap_lt hptr)
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
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_step_mkPush_cro [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (a bufRef slot ptr_rest sp0 : BitVec 64) (keys : List MessageKeyGenerator)
    (mkg : MessageKeyGenerator) (rest : List (BitVec 8))
    (hbound : keys.length ≤ maxMessageKeys)
    {st_cur : M.σ} {s0 s : State} {F : SepProp}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (hfit : FitsEvents M lim st_cur
      (if keys.length < vecCap4Of keys.length then [] else vec104GrowEvents (vecCap4Of keys.length)))
    (hpc : s.pc = chain3PCPlacedAtW ext 580#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 240#64) (halign : sp0 &&& 15#64 = 0#64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = bufRef) (hx20 : s.readReg64 .x20 = a)
    (hx24 : s.readReg64 .x24 = 104#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rest.length)
    (hnext : ∀ (sm : State),
      sm.pc = chain3PCPlacedAtW ext 168#64 → sm.status = .Running → sm.sp = sp0 - 240#64 →
      LibsignalCodeLoaded lsmpl sm.mem → sm.trace = s0.trace → Chain3MkRegs s sm →
      SepWPp (lsProg_516 (Rust.withPanics ext)) ret sm
        (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
          (∃∗ ptrMk : BitVec 64,
            vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b)
              (a + 48#64) (BitVec.ofNat 64 (vecCap4Of (keys.length + 1))) ptrMk (keys ++ [mkg])) ∗
          memRegion (sp0 - 232#64) 104 ∗
          A.pool lim
            (M.stepEvents
              (if keys.length < vecCap4Of keys.length then []
               else vec104GrowEvents (vecCap4Of keys.length)) st_cur) sm ∗
          stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_516 (Rust.withPanics ext)) ret s
      (((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        (∃∗ ptrMk : BitVec 64,
          vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b)
            (a + 48#64) (BitVec.ofNat 64 (vecCap4Of keys.length)) ptrMk keys) ∗
        prostMsgKeyAt A.repAlloc mkg (sp0 - 232#64) ∗
        A.pool lim st_cur s ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗ F)
      Q (fun _ _ => False) := by
  have hsp_align : s.spAligned = true := c3mk_push_spAligned hsp halign
  dsimp only [chain3PCPlacedAtW] at hpc hnext
  refine sepWPp_mono_pre_c3
    (P' := ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
      (∃∗ ptrMk : BitVec 64,
        vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b)
          (a + 0x30#64) (BitVec.ofNat 64 (vecCap4Of keys.length)) ptrMk keys) ∗
      A.pool lim st_cur s ∗ stackAt (sp0 - 240#64) chainMerge3SubStackX) ∗
      (prostMsgKeyAt A.repAlloc mkg (sp0 - 0xe8#64) ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine c3x_push4d_cro hC a bufRef slot ptr_rest sp0 keys rest hbound
    hfit hpc hrun hsp hsp_align hcl htr hx19 hx20 hx24 hx25 ?_
  intro s4 ptr' cap' hcap'_le hcap'_lt hptr'
    hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hregs4 hx20_4 hx24_4 hx25_4
  refine sepWPp_mono_pre_c3
    (P' := (((a + 0x30#64) ↦₆₄ cap') ∗ ((a + 0x38#64) ↦₆₄ ptr') ∗
      ((a + 0x40#64) ↦₆₄ BitVec.ofNat 64 keys.length) ∗
      (A.repAlloc).live ptr' (cap'.toNat * 104) 8 ∗
      arrayAt (fun m b => prostMsgKeyAt A.repAlloc m b) 104 ptr' keys ∗
      memRegion (ptr' + BitVec.ofNat 64 (keys.length * 104)) 104 ∗
      memRegion (ptr' + BitVec.ofNat 64 ((keys.length + 1) * 104))
        ((cap'.toNat - (keys.length + 1)) * 104) ∗
      prostMsgKeyAt A.repAlloc mkg (sp0 - 0xe8#64)) ∗
      ((bufRef ↦₆₄ slot) ∗ sliceCursorAt slot ptr_rest rest ∗
        A.pool lim
          (M.stepEvents
            (if keys.length < vecCap4Of keys.length then []
             else vec104GrowEvents (vecCap4Of keys.length)) st_cur) s4 ∗
        stackAt (sp0 - 240#64) chainMerge3SubStackX ∗ F))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine c3x_push4e_vm A.repAlloc a cap' ptr' sp0 keys mkg hcap'_le hcap'_lt hptr'
    hpc4 hrun4 hsp4 hsp_align4 hcl4 htr4 hx20_4 hx24_4 hx25_4 ?_
  intro s5 hpc5 hrun5 hsp5 hcl5 hvm5 htr5 hregs5
  refine sepWPp_mono_pre_c3 ?_
    (hnext s5 hpc5 hrun5 hsp5 hcl5 htr5 (hregs4.trans hregs5))
  rw [pool_eq_of_vm_c3 A lim
    (M.stepEvents
      (if keys.length < vecCap4Of keys.length then []
       else vec104GrowEvents (vecCap4Of keys.length)) st_cur) hvm5]
  dsimp only [cap']
  exact Entails.of_eq (by sep_ac_rfl)

private theorem c3x_mk_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    (x : ChainMergeGenGhost) (st : M.σ) (R : SepProp) (s0 : State) (k : Nat) (s : State)
    (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 4)
    (hs : c3x_LoopCroAtW M A lim ext x st R s0 k s) :
    c3x_StepAtW M A lim ext x st R s0 s (c3x_LoopCroAtW M A lim ext x st R s0 (k + 1)) := by
  rcases hs with ⟨hcro, hpc, hrun, htr, hvregs, hcl, hsp, hal, hx29, hx19, hx20, hx21,
    hx22, hx23, hx24, hx26, hx27, hx28, hOk, hlen_pay, hfit, hmem⟩
  refine c3x_segStepG_keep_cro hcro ?_
  obtain ⟨hfit_fld, hfit_next⟩ := c3x_fitsEvents_step hk hfit
  obtain ⟨mkg, hfl⟩ := chainField_eq_key_of_tag4 htag
  have hmkg_mem : mkg ∈ x.c.keys := mem_keys_of_key_mem_fields (hfl ▸ List.getElem_mem hk)
  have hseed : mkg.seed.length = 32 := hOk.2.2.2.1 mkg hmkg_mem
  have hbound : (chainGAfter x.c k).keys.length ≤ maxMessageKeys :=
    le_trans (chainGAfter_keys_length_le x.c k) hOk.2.2.2.2
  rw [hfl] at hfit_fld
  dsimp only [chainFieldStepEvents] at hfit_fld
  rw [fitsEvents_append] at hfit_fld
  rcases hfit_fld with ⟨hfit_seed, hfit_push⟩
  have halign : s0.sp &&& 15#64 = 0#64 := c3mk_sp0_aligned_of_sub_240
    (by
      have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
      rwa [hsp] at h1)
  let pfx : List (BitVec 8) :=
    encodeVarint (BitVec.ofNat 64 x.c.enc.length) ++ (x.c.fields.take k).flatMap ChainField.enc
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail
  let body : List (BitVec 8) := pbVarint 1 mkg.counter.toNat ++ pbBytes 5 mkg.seed
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
  have hlen_b : (pbVarint 1 mkg.counter.toNat ++ (pbBytes 5 mkg.seed ++ rest)).length < 2 ^ 62 := by
    dsimp only [body] at hlen_a; simp only [List.length_append] at hlen_a ⊢; omega
  have hlen_c : (pbBytes 5 mkg.seed ++ rest).length < 2 ^ 62 := by
    simp only [List.length_append] at hlen_b ⊢; omega
  have hk_lt : mkg.seed.length < 128 := by omega
  let savedRest : SepProp :=
    memRegion (s0.sp - 240#64) 8 ∗ memRegion (s0.sp - 128#64) 48 ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗ memRegion (s0.sp - 56#64) 8 ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  let mkKeysProp : SepProp :=
    ∃∗ ptrMk : BitVec 64,
      vecAt A.repAlloc 104 8 (fun m b => prostMsgKeyAt A.repAlloc m b)
        (x.a + 48#64) (BitVec.ofNat 64 (vecCap4Of (chainGAfter x.c k).keys.length))
        ptrMk (chainGAfter x.c k).keys
  have hmem_init : s.mem ⊨
      (((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 232#64) 104 ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (mkKeysProp ∗ c3x_chainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
          (x.ptr ↦ₛ pfx) ∗ savedRest)) ∗ R := by
    rw [c3x_chain3GAtCap_keys_split, hcur_open, chain3SavedRegs_c3mk_split] at hmem
    dsimp only [savedRest, mkKeysProp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  intro hL
  have hwp : SepWPp (lsProg_516 (Rust.withPanics ext)) (chain3PCPlacedAtW ext 168#64) s
      (((x.bufRef ↦₆₄ x.slot) ∗ memRegion (s0.sp - 232#64) 104 ∗
        sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
          (0x22#8 :: BitVec.ofNat 8 body.length :: (body ++ rest)) ∗
        A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s ∗
        stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
        (mkKeysProp ∗ c3x_chainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
          (x.ptr ↦ₛ pfx) ∗ savedRest))
      (fun s4 P4 =>
        s4.sp = s0.sp - 240#64 ∧ LibsignalCodeLoaded lsmpl s4.mem ∧
        s4.trace = s0.trace ∧ Chain3MkRegs s s4 ∧
        (P4 ⊢ c3x_chain3GAtCap A.repAlloc x.a
            (vecCap4Of (chainGAfter x.c (k + 1)).keys.length) (chainGAfter x.c (k + 1)) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail)
            ((x.c.fields.drop (k + 1)).flatMap ChainField.enc ++ x.tail) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c (k + 1)) st) s4 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX ∗ chain3SavedRegs s0.sp s0))
      (fun _ _ => False) := by
    refine SepWPp.bind_lscro (mid := chain3PCPlacedAtW ext 580#64)
      (Q1 := fun s2 P2 => s2.sp = s0.sp - 240#64 ∧ LibsignalCodeLoaded lsmpl s2.mem ∧
        s2.trace = s0.trace ∧ s2.readReg64 .x25 = BitVec.ofNat 64 rest.length ∧
        Chain3MkRegs s s2 ∧
        (P2 ⊢ ((x.bufRef ↦₆₄ x.slot) ∗ vecU8At A.repAlloc (s0.sp - 160#64) 0#64 1#64 [] ∗
          sliceCursorAt x.slot
            (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
              BitVec.ofNat 64 (pbVarint 1 mkg.counter.toNat).length)
            (pbBytes 5 mkg.seed ++ rest) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s2 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (vecU8 A.repAlloc (s0.sp - 232#64) [] ∗ vecU8 A.repAlloc (s0.sp - 208#64) [] ∗
            vecU8 A.repAlloc (s0.sp - 184#64) [] ∗
            ((s0.sp - 136#64) ↦₃₂ mkg.counter) ∗ memRegion (s0.sp - 132#64) 4 ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ pbVarint 1 mkg.counter.toNat) ∗
            mkKeysProp ∗ c3x_chainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))) hcro ?_ ?_
    · refine step_mkHead_cro hC x.bufRef x.slot (x.ptr + BitVec.ofNat 64 pfx.length)
        s0.sp body rest x.tail hmk_lt htail_le hlen_a hpc hrun hsp halign hcl htr
        hx19 hx21 hx22 hx23 ?_
      intro s1 hpc1 hrun1 hsp1 hcl1 htr1 hx25_1 hregs1
      dsimp only [body]
      rw [List.append_assoc (pbVarint 1 mkg.counter.toNat) (pbBytes 5 mkg.seed) rest]
      refine sepWPp_mono_pre_c3
        (P' := ((x.bufRef ↦₆₄ x.slot) ∗ ((s0.sp - 136#64) ↦₃₂ 0#32) ∗
          sliceCursorAt x.slot (x.ptr + BitVec.ofNat 64 pfx.length + 2#64)
            (pbVarint 1 mkg.counter.toNat ++ (pbBytes 5 mkg.seed ++ rest)) ∗
          A.pool lim (M.stepEvents (chainDoneEvents x.c k) st) s1 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (vecU8 A.repAlloc (s0.sp - 232#64) [] ∗ vecU8 A.repAlloc (s0.sp - 208#64) [] ∗
            vecU8 A.repAlloc (s0.sp - 184#64) [] ∗
            vecU8At A.repAlloc (s0.sp - 160#64) 0#64 1#64 [] ∗
            memRegion (s0.sp - 132#64) 4 ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            mkKeysProp ∗ c3x_chainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))
        (by dsimp only [body]; exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine step_mkCnt_cro hC x.bufRef x.slot
        (x.ptr + BitVec.ofNat 64 pfx.length + 2#64) s0.sp mkg.counter (pbBytes 5 mkg.seed) rest
        hlen_b hpc1 hrun1 hsp1 halign hcl1 htr1 (hregs1.1.trans hx19) hx25_1 ?_
      intro s2 hpc2 hrun2 hsp2 hcl2 htr2 hx25_2 hregs2
      refine SepWPp.done hpc2 hrun2 ⟨hsp2, hcl2, htr2, hx25_2, hregs1.trans hregs2, ?_⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 P2 hpc2 hrun2 hcro2 ⟨hsp2, hcl2, htr2, hx25_2, hregs12, hent2⟩
      refine sepWPp_mono_pre_c3 hent2 ?_
      refine c3x_step_mkSeed_cro hC x.bufRef x.slot
        (x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
          BitVec.ofNat 64 (pbVarint 1 mkg.counter.toNat).length)
        s0.sp mkg.seed rest hk_lt hlen_c hfit_seed hcro2 hpc2 hrun2 hsp2 halign hcl2 htr2
        (hregs12.1.trans hx19) (hregs12.2.2.2.1.trans hx22) hx25_2 ?_
      intro s3 hpc3 hrun3 hsp3 hcl3 htr3 hx25_3 hregs3
      have hregs13 : Chain3MkRegs s s3 := hregs12.trans hregs3
      let ptrAfterSeed : BitVec 64 :=
        x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
          BitVec.ofNat 64 (pbVarint 1 mkg.counter.toNat).length +
          BitVec.ofNat 64 (pbBytes 5 mkg.seed).length
      refine sepWPp_mono_pre_c3
        (P' := ((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot ptrAfterSeed rest ∗
          mkKeysProp ∗
          prostMsgKeyAt A.repAlloc mkg (s0.sp - 232#64) ∗
          A.pool lim
            (M.stepEvents (bytesMergeEvents 0 mkg.seed.length)
              (M.stepEvents (chainDoneEvents x.c k) st)) s3 ∗
          stackAt (s0.sp - 240#64) chainMerge3SubStackX) ∗
          (((x.ptr + BitVec.ofNat 64 pfx.length) ↦ₛ [0x22#8, BitVec.ofNat 8 body.length]) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64) ↦ₛ pbVarint 1 mkg.counter.toNat) ∗
            ((x.ptr + BitVec.ofNat 64 pfx.length + 2#64 +
              BitVec.ofNat 64 (pbVarint 1 mkg.counter.toNat).length) ↦ₛ pbBytes 5 mkg.seed) ∗
            c3x_chainNoKeys A.repAlloc x.a (chainGAfter x.c k) ∗
            (x.ptr ↦ₛ pfx) ∗ savedRest))
        (by
          rw [← @c3mk_prostMsgKeyAt_fold A.repAlloc s0.sp mkg]
          dsimp only [ptrAfterSeed, mkKeysProp]
          exact Entails.of_eq (by sep_ac_rfl)) ?_
      refine c3x_step_mkPush_cro hC x.a x.bufRef x.slot ptrAfterSeed s0.sp
        (chainGAfter x.c k).keys mkg rest hbound hfit_push
        hpc3 hrun3 hsp3 halign hcl3 htr3
        (hregs13.1.trans hx19) (hregs13.2.1.trans hx20) (hregs13.2.2.2.2.2.1.trans hx24) hx25_3 ?_
      intro s4 hpc4 hrun4 hsp4 hcl4 htr4 hregs4
      have hregs : Chain3MkRegs s s4 := hregs13.trans hregs4
      refine SepWPp.done hpc4 hrun4 ⟨hsp4, hcl4, htr4, hregs, ?_⟩
      have hlen_succ : (chainGAfter x.c (k + 1)).keys.length = (chainGAfter x.c k).keys.length + 1 := by
        rw [chainGAfter_succ_of_key hk hfl]; simp [ChainG.apply]
      have hdone_succ :
          M.stepEvents
            (if (chainGAfter x.c k).keys.length < vecCap4Of (chainGAfter x.c k).keys.length then []
             else vec104GrowEvents (vecCap4Of (chainGAfter x.c k).keys.length))
            (M.stepEvents (bytesMergeEvents 0 mkg.seed.length)
              (M.stepEvents (chainDoneEvents x.c k) st)) =
          M.stepEvents (chainDoneEvents x.c (k + 1)) st := by
        rw [← M.stepEvents_append (bytesMergeEvents 0 mkg.seed.length) _
          (M.stepEvents (chainDoneEvents x.c k) st),
          ← M.stepEvents_append (chainDoneEvents x.c k) _ st,
          c3x_chainDoneEvents_succ hk, hfl]
        rfl
      rw [hdone_succ, hlen_succ, chainGAfter_succ hk, hfl,
        c3x_chain3GAtCap_apply_key, chain3SavedRegs_c3mk_split,
        ← sliceCursorAfter_tag4_combine x.slot x.ptr (x.c.payload ++ x.tail) pfx
          (pbVarint 1 mkg.counter.toNat) (pbBytes 5 mkg.seed) rest hpay_eq]
      dsimp only [body, savedRest, ptrAfterSeed, rest]
      exact Entails.of_eq (by sep_ac_rfl)
  obtain ⟨s4, hsteps, hex⟩ := hwp R hmem_init hL
  rcases hex with ⟨hpc4, hrun4, P4, hm4, hsp4, hcl4, htr4, hregs, hent4⟩ |
    ⟨_, _, _, hpan⟩ | ⟨_, hoom⟩
  · have hal4 : s4.spAligned = true := by simp only [State.spAligned, hsp4, ← hsp]; exact hal
    have hmem4 := Satisfies.mono (sepConj_mono_left hent4) hm4
    simp only [sepConj_assoc] at hmem4
    exact ⟨s4, hsteps, Or.inl ⟨hpc4, hrun4, htr4, hregs.2.2.2.2.2.2.2.2.2.2.trans hvregs,
      hcl4, hsp4, hal4, hregs.2.2.2.2.2.2.2.2.2.1.trans hx29, hregs.1.trans hx19,
      hregs.2.1.trans hx20, hregs.2.2.1.trans hx21, hregs.2.2.2.1.trans hx22,
      hregs.2.2.2.2.1.trans hx23, hregs.2.2.2.2.2.1.trans hx24,
      hregs.2.2.2.2.2.2.1.trans hx26, hregs.2.2.2.2.2.2.2.1.trans hx27,
      hregs.2.2.2.2.2.2.2.2.1.trans hx28, hOk, hlen_pay, hfit_next, hmem4⟩⟩
  · exact hpan.elim
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem c3x_loop_run [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext)
    {x : ChainMergeGenGhost} {st : M.σ} {R : SepProp} {s0 : State} :
    ∀ (rem k : Nat) (s : State), k + rem = x.c.fields.length →
      c3x_LoopCroAtW M A lim ext x st R s0 k s →
      reaches_outcome (lsProg_516 (Rust.withPanics ext))
        (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) (x, st) R s0 s
  | 0, k, s, hkr, ⟨_hcro, hs⟩ => by
      have hk : k = x.c.fields.length := by omega
      subst hk
      apply reaches_outcome.of_codeLoaded
      intro hL
      obtain ⟨sf, hst, ⟨hret, hcc, hm⟩ | ⟨hpan, hmpan⟩⟩ :=
        c3x_exit_ok ext x st R s0 s hs hL
      · exact Arm64.reaches_outcome_steps hst
          (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hm⟩))
      · exact Arm64.reaches_outcome_steps hst
          (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hmpan⟩)))
  | rem + 1, k, s, hkr, hs => by
      have hk : k < x.c.fields.length := by omega
      have hk' : (k + 1) + rem = x.c.fields.length := by omega
      rcases chainField_tag_cases (x.c.fields[k]'hk) with h12 | h3 | h4
      · exact segStepG_then (c3x_srk_ok ext hC x st R s0 k s hk h12 hs)
          (fun s' hs' => c3x_loop_run ext hC rem (k + 1) s' hk' hs')
      · exact segStepG_then (c3x_ck_ok ext hC x st R s0 k s hk h3 hs)
          (fun s' hs' => c3x_loop_run ext hC rem (k + 1) s' hk' hs')
      · exact segStepG_then (c3x_mk_ok ext hC x st R s0 k s hk h4 hs)
          (fun s' hs' => c3x_loop_run ext hC rem (k + 1) s' hk' hs')

end ExactLoopProof

/-! ## Core Exact-Trace Block-`516` Theorem and Corollaries -/

/-- `message::merge<Chain> [local#4]` (Block `516`) on `lsProg_516 (Rust.withPanics ext)` meets `c3x_chainMerge3ExactCapRawSpecW A lim` under `StoreKit.withLsCodeRoLoaded`, emitting `chainMergeEvents x.c`. -/
theorem c3x_chainMerge3W_exact_cap_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) := by
  apply subroutine_ok.of_codeLoaded
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal _hL
  exact segStepG_then (c3x_entry_ok hC x st R s0 hpc hrun hpre hal) fun s hs =>
    c3x_loop_run ext hC x.c.fields.length 0 s (Nat.zero_add _) hs

theorem c3x_chainMerge3W_exact_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (ext : LibsignalHooks)
    (hC : Chain3CalleesCroPlacedW M A lim ext) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim)) :=
  subroutine_ok_mono (c3x_chainMerge3W_exact_cap_cro_placed_ok ext hC)
    (fun _ _ _ hp => hp)
    (fun ⟨x, st⟩ R s0 sf hq => by
      dsimp only [withLsCodeRoLoaded, c3x_chainMerge3ExactCapRawSpecW,
        c3x_chainMerge3ExactRawSpecW] at hq ⊢
      exact Satisfies.mono
        (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
          (c3x_chain3GAtCap_entails_prostChainGAt A.repAlloc x.a (vecCap4Of x.c.keys.length) x.c))))
        hq)
    (hpanic := fun _ _ _ _ hp => hp)
    (hexit := fun _ _ _ _ _ he => he)
    (hoom := fun _ _ _ _ ho => ho)

private theorem c3x_chainMerge5_cro_transfer [LibsignalPlacement] {α : Type}
    {ext : LibsignalHooks} {callerProg : Program} {callerBlk : Nat}
    [hcaller : IsLsBlockProg callerProg callerBlk ext] {S : Spec α}
    (hC5 : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl S)) :
    subroutine_ok callerProg (lsmpl.base 516) (withLsCodeRoLoaded lsmpl S) := by
  apply subroutine_ok_outcome_intro
  intro xst R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hcallee : IsLsBlockProg (lsProg_516 (Rust.withPanics ext)) 516 (Rust.withPanics ext) :=
    inferInstance
  have hQL : (lsProg_516 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hcallee.eq_blockProgram ▸
      hcrl0.1 516 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hC5.no_fault_before_outcome xst R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (lsProg_516 (Rust.withPanics ext)).externAt? pc =
      callerProg.externAt? pc :=
    ls_externAt?_withPanics_eq (prog1 := lsProg_516 (Rust.withPanics ext)) (prog2 := callerProg)
  have hsvc : (lsProg_516 (Rust.withPanics ext)).svc = callerProg.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

/-- Cross-block caller lift of `c3x_chainMerge3ExactCapRawSpecW` to any `callerProg` over `ext`
(`[IsLsBlockProg callerProg callerBlk ext]`, e.g. `lsProg_518 ext`). -/
theorem c3x_chainMerge5_exact_cap_cro_of_block [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hC5 : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim))) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) :=
  c3x_chainMerge5_cro_transfer hC5

theorem c3x_chainMerge5_exact_cro_of_block [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hC5 : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim))) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim)) :=
  c3x_chainMerge5_cro_transfer hC5

theorem c3x_chainMerge3W_exact_cap_cro_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) :=
  c3x_chainMerge3W_exact_cap_cro_placed_ok ext
    (chain3CalleesCro_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem c3x_chainMerge3W_exact_cro_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim)) :=
  c3x_chainMerge3W_exact_cro_placed_ok ext
    (chain3CalleesCro_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem c3x_chainMerge5_exact_cap_cro_of_block_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactCapRawSpecW A lim)) :=
  c3x_chainMerge5_exact_cap_cro_of_block
    (c3x_chainMerge3W_exact_cap_cro_placed_ok_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem c3x_chainMerge5_exact_cro_of_block_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk ext]
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok callerProg (lsmpl.base 516)
      (withLsCodeRoLoaded lsmpl (c3x_chainMerge3ExactRawSpecW A lim)) :=
  c3x_chainMerge5_exact_cro_of_block
    (c3x_chainMerge3W_exact_cro_placed_ok_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_raw)

theorem c3x_chainMerge5ExactCapCroPlacedOkExt_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    c3x_ChainMerge5ExactCapCroPlacedOkExt A lim ext :=
  c3x_chainMerge5_exact_cap_cro_of_block_hooks (callerProg := lsProg_518 ext)
    hshim halloc hrealloc hdealloc hmc hpanic_raw

theorem c3x_chainMerge5ExactCroPlacedOkExt_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    c3x_ChainMerge5ExactCroPlacedOkExt A lim ext :=
  c3x_chainMerge5_exact_cro_of_block_hooks (callerProg := lsProg_518 ext)
    hshim halloc hrealloc hdealloc hmc hpanic_raw

private theorem c3x_cli_noAllocShim_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (hShim : gh.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec :=
  (show lsRustNoAllocShimSymCli = lsRustNoAllocShimSym by decide) ▸
    ⟨hookNoop, (cliGhostExterns_shim gh (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
      noAllocShim_hookOk⟩

private theorem c3x_cli_framelessMemcpy_sat [LibsignalPlacement]
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

theorem c3x_chainMerge5ExactCapCroPlacedOkExt_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    c3x_ChainMerge5ExactCapCroPlacedOkExt A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  c3x_chainMerge5ExactCapCroPlacedOkExt_of_hooks (c3x_cli_noAllocShim_sat mmpl gh W hA.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
    (c3x_cli_framelessMemcpy_sat mmpl gh W hA)
    (cliGhostExterns_panic_handle_error mmpl gh W)

theorem c3x_chainMerge5ExactCapCroPlacedOkExt_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    c3x_ChainMerge5ExactCapCroPlacedOkExt A lim
      (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  c3x_chainMerge5ExactCapCroPlacedOkExt_cli mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

theorem c3x_chainMerge5ExactCroPlacedOkExt_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    c3x_ChainMerge5ExactCroPlacedOkExt A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  c3x_chainMerge5ExactCroPlacedOkExt_of_hooks (c3x_cli_noAllocShim_sat mmpl gh W hA.shim_eq)
    ((show lsRustAllocSymCli = lsRustAllocSym by decide) ▸
      cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
    ((show lsRustReallocSymCli = lsRustReallocSym by decide) ▸
      cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
    ((show lsRustDeallocSymCli = lsRustDeallocSym by decide) ▸
      cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
    (c3x_cli_framelessMemcpy_sat mmpl gh W hA)
    (cliGhostExterns_panic_handle_error mmpl gh W)

theorem c3x_chainMerge5ExactCroPlacedOkExt_of_cliHooks [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks A lim) :
    c3x_ChainMerge5ExactCroPlacedOkExt A lim
      (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  c3x_chainMerge5ExactCroPlacedOkExt_cli mmpl bumpGhost W (cliAllocHooks_to_bumpGhost hA)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3ExactPlacedBudget
