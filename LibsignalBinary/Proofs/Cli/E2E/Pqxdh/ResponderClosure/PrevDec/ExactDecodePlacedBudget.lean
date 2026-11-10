/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxD

/-!
# Exact-Trace Budget Verification of Inlined `SessionStructure::decode` on Block `518`

Proves that Block `518`'s inlined `SessionStructure::decode` (`(blkPl_518).base + 0x1ee8 → +0x2620`)
on `lsProg_518 ext`, executed on `enc = encSession sess` under `OverPrevEncOKAt enc sess`, emits
exact allocation trace `evs = sessDeserEvents ⟨some sess⟩` (`SessDeserializeCancelEnv ⟨some sess⟩`),
parameterized by the exact-trace `message::merge<Chain>` contract on Block `516`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (MessageKeyGenerator maxReceiverChains)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement
  lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsRustReallocSym
  lsmpl withLsCl
)
open CryptoVerification.RustHeap (RustAlloc arrayAt arrayAt_concat vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks104_6QWAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.E2E.Record.L1GX (GenFieldX genFieldsX kyberAt pidAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG ChainMergeGenGhost GenField SSG prostChainGAt prostMsgKeyAt
)
open Symbolic.Swarm.TRREF.B3Defs (DeserializeScopeP_Q NonEmptyV1Q)
open Symbolic.Swarm.TRREF.B3DeserQ (
  ExtraGQ GenFieldQ SSGQ genFieldsQ noPq_of_mem_genFieldsX prostSSGQAt
  recFieldsQ ssgqAfter ssgqOf
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  OverDecSenderField chain3GAt chain3GAt_entails_prostChainGAt chain3VecAt chainGRest
  chainMerge3StackX default_cells_entail_chain3VecAt overDecArmOff overDecChain_cursor_unsplit
  overDecChain_mem96 overDecChain_payload_suffix overDecChain_stack_split overDecWt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  clearPending scopeIn_clearPending
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecAnyField OverDecBytesField OverDecFreshChain OverDecG OverDecRecvField
  OverDecRegsCroPlaced OverDecRegsPlaced OverDecSavedRegs OverDecVarintField OverPrevEncOK
  OverPrevEncOKAt SepWPp_exists_left_rc SepWPp_pure_left_rc
  chunks104_6QWAt_read_a90_eq_rc chunks104_6QWAt_write_eq_rc len_ne_cap_of_lt_rc
  memRegion104_bf0_join_rc memRegion104_eq_exists_chunks104_6QWAt_rc memRegion128_bf0_split_80_24_24
  memRegion344_a90_join_rc memRegion344_a90_split_rc ofNat_length_eq_cap_of_eq_rc
  overDecFreshChain_cons_inv overDecScratchPre overDecStackX overDec_encSession_eq
  overDec_encSession_length_lt overDec_enc_ne_nil overDec_exit_ext overDec_flatMap_cons
  overDec_flatMap_ne_nil overDec_fold_genFieldsQ overDec_freshChain_genFieldsQ
  overDec_genFieldsQ_ne_nil overDec_mem_genFieldsQ overDec_sepWPp_mono_post overDec_sepWPp_seq
  overDec_sepWPp_weaken_pre overPrevElemRestExt payload_append_length_lt62_of_suffix
  prostChainGAt_move_chunks104_rc sliceCursorAfter_split_of_suffix_recv
  sliceCursorAfter_unsplit_of_suffix_recv stackAt_overDecStackX_eq_chainMerge3StackX
  suffix_payload_of_suffix_enc_recv vecBuf_recv_full_open_rc_ext vecBuf_recv_not_full_open_rc_ext
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
  fitsEvents_append fitsEvents_nil
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemmoveBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  AllocContractsPlaced GrowOne104Env finishGrowStackX growOne104Events growOne104SpecX
  growOneChainSpecX growOneChainStackX growOneChain_placed_ok_cl growOneChain_placed_ok_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  vec104GrowEvents vecCap4Of
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.ChainBudget (chainMergeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.MergeFieldBasicBudget (
  GenFieldQ.FreshBytes mergeFieldQEvents nextCapRecv
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget (
  fieldsEventsAux freshBytes_ssgqAfter nextCapRecv_eq_vecCap4Of sessDeserEvents
)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (deserCancelFineMaxReq)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget (
  growOne_plain_pre_eq_q_ext
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  stackAt_sub_eq_pl step_2114_to_2160_placed_budget step_2310_to_2114_of_ne_placed_budget
  step_2310_to_growOne_of_eq_placed_budget step_234c_to_2114_placed_budget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  overDecHeapBudget overDecScratchPostBudget overPrevElemAtBudget overPrevElemRestBudget
  sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux (
  SepWPp_bind_sepWP_frame SepWPp_bind_sepWP_frame_cro SepWPp_call_frame_cro_noPanic
  SepWPp_ret_sepWP_frame SepWPp_weaken_frame overDecChain_segA_placed_budget
  overDecChain_segB_placed_budget overDecRecv_pre_step_80_placed_budget toChain3GTop
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6PlacedBudget (
  BytesMerge6Placed514OkExtW bytes_merge_6_placed_ok_w_cro
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (VerNeS1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (VerNeTailEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxA (
  b518x_entry_cro_placed b518x_headCons_cro_placed b518x_headNil_cro_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxB (
  b518x_key_cro_placed_of_alloc
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxC (
  b518x_arm_varint_cro_placed_of_alloc
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudgetAuxD (
  b518x_arm_bytes_cro_placed_of_bm6w
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Block-`516` Exact `message::merge<Chain>` Contract Parameter -/

/-- Exact-trace raw contract of `prost::encoding::message::merge::<Chain, &mut &[u8]>`
(Block `516`, `lsmpl.base 516`) at `chainMerge3StackX`, tightening
`TopPlacedBudgetAux.chainMerge3RawSpecW` from `ChainMergeGenEnv x` to `evs = chainMergeEvents x.c`. -/
def b518x_chainMerge3ExactSpecW {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents x.c)⌝ ∗
      chain3GAt A.repAlloc x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMerge3StackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A.repAlloc x.a x.c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool lim (M.stepEvents (chainMergeEvents x.c) st) sf ∗ stackAt s0.sp chainMerge3StackX

/-- Relocatable `[LibsignalPlacement]` exact-trace Block-`516` (`lsmpl.base 516`) contract parameter on `lsProg_518 ext` under `withLsCodeRoLoaded lsmpl`. -/
def b518x_ChainMerge5ExactCroPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
    (withLsCodeRoLoaded lsmpl (b518x_chainMerge3ExactSpecW A lim))

/-! ## Capacity-Pinned Block-`516` Contract and `SSGQ` Invariant -/

/-- The `message_keys` (pinned at capacity `capMk`) and `chain_key` fields of `prostChainGAt A a c`
(definitionally identical to `Chain3ExactPlacedBudget.c3x_chainGRestCap`). -/
def b518x_chainGRestCap (A : RustAlloc) (a : BitVec 64) (capMk : Nat) (c : ChainG) : SepProp :=
  (∃∗ ptrMk : BitVec 64,
    vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b)
      (a + 0x30#64) (BitVec.ofNat 64 capMk) ptrMk c.keys) ∗
    match c.ck with
    | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
    | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
        memRegion (a + 0x64#64) 4

/-- Capacity-pinned `chain3GAt`: `srk` and `priv` as `chain3VecAt` (`cap = 0#64` when `[]`) and
`keys` pinned at capacity `BitVec.ofNat 64 capMk` (`0` at both Block-`518` call sites `+0x9c0` and
`+0xbf0`; definitionally identical to `Chain3ExactPlacedBudget.c3x_chain3GAtCap`). -/
def b518x_chain3GAtCap (A : RustAlloc) (a : BitVec 64) (capMk : Nat) (c : ChainG) : SepProp :=
  chain3VecAt A a c.srk ∗ chain3VecAt A (a + 0x18#64) c.priv ∗ b518x_chainGRestCap A a capMk c

theorem b518x_chainGRestCap_entails_chainGRest (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    b518x_chainGRestCap A a capMk c ⊢ chainGRest A a c := by
  unfold b518x_chainGRestCap chainGRest vecOf
  refine sepConj_mono_left ?_
  refine Entails.sepExists_elim fun ptrMk => ?_
  exact Entails.sepExists_right (BitVec.ofNat 64 capMk)
    (Entails.sepExists_right ptrMk (Entails.refl _))

theorem b518x_chain3GAtCap_entails_chain3GAt (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    b518x_chain3GAtCap A a capMk c ⊢ chain3GAt A a c := by
  unfold b518x_chain3GAtCap chain3GAt
  exact sepConj_mono_right (sepConj_mono_right (b518x_chainGRestCap_entails_chainGRest A a capMk c))

theorem b518x_chain3GAtCap_entails_prostChainGAt (A : RustAlloc) (a : BitVec 64)
    (capMk : Nat) (c : ChainG) :
    b518x_chain3GAtCap A a capMk c ⊢ prostChainGAt A a c :=
  Entails.trans (b518x_chain3GAtCap_entails_chain3GAt A a capMk c)
    (chain3GAt_entails_prostChainGAt A a c)

theorem b518x_default_cells_entail_c3KeysCap (A : RustAlloc) (v : BitVec 64) :
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

theorem b518x_default_cells_entail_chain3GAtCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
    ((a + 0x18#64) ↦₆₄ 0#64) ∗ ((a + 0x20#64) ↦₆₄ 1#64) ∗ ((a + 0x28#64) ↦₆₄ 0#64) ∗
    ((a + 0x30#64) ↦₆₄ 0#64) ∗ ((a + 0x38#64) ↦₆₄ 8#64) ∗ ((a + 0x40#64) ↦₆₄ 0#64) ∗
    ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 ⊢
      b518x_chain3GAtCap A a 0 ChainG.empty := by
  have h1 : a + 0x18#64 + 8#64 = a + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have h2 : a + 0x18#64 + 16#64 = a + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  have h3 : a + 0x30#64 + 8#64 = a + 0x38#64 := by rw [BitVec.add_assoc]; rfl
  have h4 : a + 0x30#64 + 16#64 = a + 0x40#64 := by rw [BitVec.add_assoc]; rfl
  have hv1 := default_cells_entail_chain3VecAt A a
  have hv2 := default_cells_entail_chain3VecAt A (a + 0x18#64)
  have hv3 := b518x_default_cells_entail_c3KeysCap A (a + 0x30#64)
  rw [h1, h2] at hv2
  rw [h3, h4] at hv3
  unfold b518x_chain3GAtCap b518x_chainGRestCap ChainG.empty
  dsimp only
  refine Entails.trans ?_
    (sepConj_mono hv1 (sepConj_mono hv2 (sepConj_mono_left hv3)))
  exact Entails.of_eq (by sep_ac_rfl)

/-- Tag-6 (`sender_chain`, `q + 0x9c0#64`) pre-call bridge into `b518x_chain3GAtCap A (q + 0x9c0#64) 0 ChainG.empty`. -/
theorem b518x_overDecChain_bridge_ext (A : RustAlloc) (q : BitVec 64) :
    ((q + 0x9c0#64) ↦₆₄ 0#64) ∗ ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗
    ((q + 0x9d8#64) ↦₆₄ 0#64) ∗ ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗
    ((q + 0x9f0#64) ↦₆₄ 0#64) ∗ ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
    ((q + 0xa08#64) ↦₆₄ noneCap) ∗ memRegion (q + 0xa10#64) 24 ⊢
      b518x_chain3GAtCap A (q + 0x9c0#64) 0 ChainG.empty := by
  have h := b518x_default_cells_entail_chain3GAtCap A (q + 0x9c0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- Tag-7 (`receiver_chains`, `q + 0xbf0#64`) pre-call bridge into `b518x_chain3GAtCap A (q + 0xbf0#64) 0 ChainG.empty`. -/
theorem b518x_default_cells_bf0_entail_chain3GAtCap_ext (A : RustAlloc) (q : BitVec 64) :
    (((q + 0xbf0#64) ↦₆₄ 0#64) ∗
    ((q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((q + 0xc00#64) ↦₆₄ 0#64) ∗ ((q + 0xc08#64) ↦₆₄ 0#64) ∗
    ((q + 0xc10#64) ↦₆₄ 1#64) ∗ ((q + 0xc18#64) ↦₆₄ 0#64) ∗ ((q + 0xc20#64) ↦₆₄ 0#64) ∗
    ((q + 0xc28#64) ↦₆₄ 8#64) ∗ ((q + 0xc30#64) ↦₆₄ 0#64) ∗
    ((q + 0xc38#64) ↦₆₄ noneCap)) ∗ memRegion (q + 0xc40#64) 24 ⊢
      b518x_chain3GAtCap A (q + 0xbf0#64) 0 ChainG.empty := by
  have h := b518x_default_cells_entail_chain3GAtCap A (q + 0xbf0#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h ⊢
  exact h

/-- Capacity-pinned exact-trace raw contract of `prost::encoding::message::merge::<Chain, &mut &[u8]>` (Block `516`, `lsmpl.base 516`) at `chainMerge3StackX` (`capMk = 0` on entry). -/
def b518x_chainMerge3ExactSpecW' {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents x.c)⌝ ∗
      b518x_chain3GAtCap A.repAlloc x.a 0 ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMerge3StackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostChainGAt A.repAlloc x.a x.c ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
      A.pool lim (M.stepEvents (chainMergeEvents x.c) st) sf ∗ stackAt s0.sp chainMerge3StackX

/-- Capacity-pinned relocatable `[LibsignalPlacement]` exact-trace Block-`516` (`lsmpl.base 516`) contract on `lsProg_518 ext` under `withLsCodeRoLoaded lsmpl`. -/
def b518x_ChainMerge5ExactCroPlacedOkExt' [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
    (withLsCodeRoLoaded lsmpl (b518x_chainMerge3ExactSpecW' A lim))

/-- Precondition strengthening bridge (`b518x_chain3GAtCap ⊢ chain3GAt`) showing the unpinned
parameter implies the cap-pinned parameter. -/
theorem b518x_chainMerge5Exact_pinned_of_unpinned [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : b518x_ChainMerge5ExactCroPlacedOkExt A lim ext) :
    b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext :=
  subroutine_ok_mono h
    (fun (x, st) s R hpre => by
      dsimp only [withLsCodeRoLoaded, b518x_chainMerge3ExactSpecW', b518x_chainMerge3ExactSpecW] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      exact sepConj_mono_right (sepConj_mono_left
        (b518x_chain3GAtCap_entails_chain3GAt A.repAlloc x.a 0 ChainG.empty)))
    (fun _ _ _ _ hq => hq)

/-- Capacity-0-when-empty `Vec<u8>` at `p` for `SessionStructure` byte fields (`lik`, `rik`, `root`,
`abk`, `pq`): pins `cap = 0#64` while `bs = []`, and collapses to `vecU8 A p bs` once `bs ≠ []`. -/
def b518x_vecU8Fresh0 (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if bs = [] then ∃∗ ptr : BitVec 64, vecU8At A p 0#64 ptr []
  else vecU8 A p bs

theorem b518x_vecU8Fresh0_entails_vecU8 (A : RustAlloc) (p : BitVec 64) (bs : List (BitVec 8)) :
    b518x_vecU8Fresh0 A p bs ⊢ vecU8 A p bs := by
  unfold b518x_vecU8Fresh0
  split_ifs with h
  · subst h
    unfold vecU8
    exact Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right 0#64 (Entails.sepExists_right ptr (Entails.refl _))
  · exact Entails.refl _

/-- Capacity-explicit `prostSSGQAt` loop invariant for Block `518`:
- basic `Vec<u8>` fields (`lik`, `rik`, `root`, `abk`, `pq`) as `b518x_vecU8Fresh0` (`cap = 0` when `[]`);
- `receiver_chains` pinned at deterministic doubling capacity `BitVec.ofNat 64 (vecCap4Of v.base.recv.length)`. -/
def b518x_prostSSGQAtCap (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  b518x_vecU8Fresh0 A ss v.base.lik ∗
    b518x_vecU8Fresh0 A (ss + 0x18#64) v.base.rik ∗
    b518x_vecU8Fresh0 A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAt A a c)
        (ss + 0x48#64) (BitVec.ofNat 64 (vecCap4Of v.base.recv.length)) ptrRecv v.base.recv) ∗
    b518x_vecU8Fresh0 A (ss + 0x60#64) v.ext.abk ∗
    b518x_vecU8Fresh0 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem b518x_prostSSGQAtCap_entails_prostSSGQAt (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    b518x_prostSSGQAtCap A ss v ⊢ prostSSGQAt A ss v := by
  unfold b518x_prostSSGQAtCap prostSSGQAt vecOf
  refine sepConj_mono (b518x_vecU8Fresh0_entails_vecU8 A ss v.base.lik) ?_
  refine sepConj_mono (b518x_vecU8Fresh0_entails_vecU8 A (ss + 0x18#64) v.base.rik) ?_
  refine sepConj_mono (b518x_vecU8Fresh0_entails_vecU8 A (ss + 0x30#64) v.base.root) ?_
  refine sepConj_mono
    (Entails.sepExists_elim fun ptrRecv =>
      Entails.sepExists_right (BitVec.ofNat 64 (vecCap4Of v.base.recv.length))
        (Entails.sepExists_right ptrRecv (Entails.refl _))) ?_
  refine sepConj_mono (b518x_vecU8Fresh0_entails_vecU8 A (ss + 0x60#64) v.ext.abk) ?_
  exact sepConj_mono_left (b518x_vecU8Fresh0_entails_vecU8 A (ss + 0x78#64) v.ext.pq)

/-- Capacity-explicit Block-`518` decode-loop spatial invariant (`overDecHeapBudget` with
`prostSSGQAt` strengthened to `b518x_prostSSGQAtCap`). -/
def b518x_overDecHeapCap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) : SepProp :=
  overPrevElemRestBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    b518x_prostSSGQAtCap A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

theorem b518x_overDecHeapCap_entails_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) :
    b518x_overDecHeapCap A lim st s g rest v ⊢ overDecHeapBudget A lim st s g rest v := by
  unfold b518x_overDecHeapCap overDecHeapBudget
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (b518x_prostSSGQAtCap_entails_prostSSGQAt A.repAlloc (g.q + 0x930#64) v))))

/-! ## `VerNeSessionCancelEnv` Envelopes and Scope Bridges -/

/-- Allocation envelope for `SessionStructure` bytes `enc = encSession s` paired with `SessDeserializeCancelEnv ⟨some s⟩`. -/
def b518x_VerNeSessionCancelRawEnv (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ s : Session (List (BitVec 8)),
    enc = encSession s ∧
    SessDeserializeCancelEnv ⟨some s⟩ evs

/-- `b518x_VerNeSessionCancelRawEnv` augmented with the `2 MiB` record-byte bound `(encodeRecord ⟨some s⟩).length ≤ deserCancelFineMaxReq`. -/
def b518x_VerNeSessionCancelEnv (enc : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ s : Session (List (BitVec 8)),
    enc = encSession s ∧
    (encodeRecord ⟨some s⟩).length ≤ deserCancelFineMaxReq ∧
    SessDeserializeCancelEnv ⟨some s⟩ evs

/-- Composite version-mismatch path allocation envelope parameterized by session-decode envelope `DecEnv`. -/
def b518x_VerNeTightTopEnvOf (DecEnv : List (BitVec 8) → List AllocEvent → Prop)
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv VerNeS1Env (SeqEnv (SeqEnv (DecEnv enc) FreeOnlyEvs) VerNeTailEnv)

abbrev b518x_VerNeTightTopRawEnv : List (BitVec 8) → List AllocEvent → Prop :=
  b518x_VerNeTightTopEnvOf b518x_VerNeSessionCancelRawEnv

abbrev b518x_VerNeTightTopEnv : List (BitVec 8) → List AllocEvent → Prop :=
  b518x_VerNeTightTopEnvOf b518x_VerNeSessionCancelEnv

/-- Definitional telescope: `fieldsEventsAux 0 0 (genFieldsQ s)` is definitionally equal to
`sessDeserEvents ⟨some s⟩` (`recFieldsQ ⟨some s⟩ = genFieldsQ s`). -/
theorem b518x_fieldsEventsAux_genFieldsQ_eq_sessDeserEvents
    (s : Session (List (BitVec 8))) :
    fieldsEventsAux 0 0 (genFieldsQ s) = sessDeserEvents ⟨some s⟩ :=
  rfl

/-- Any `s_old` with `Cli.Slots.scopeIn ⟨some s_old⟩` and `s_old.state.sessionVersion = 4#32` satisfies `OverPrevEncOKAt (encSession (clearPending s_old)) (clearPending s_old)`. -/
theorem b518x_overPrevEncOKAt_clearPending_of_scopeIn
    {s_old : Session (List (BitVec 8))}
    (h : CryptoVerification.SignalSession.Cli.Slots.scopeIn ⟨some s_old⟩)
    (hver : s_old.state.sessionVersion = 4#32) :
    OverPrevEncOKAt (encSession (clearPending s_old)) (clearPending s_old) :=
  ⟨rfl, CryptoVerification.SignalSession.Cli.Slots.scopeKit_of_scopeIn (scopeIn_clearPending h),
    hver, rfl, rfl⟩

/-- Satisfiability of `SessDeserializeCancelEnv` and `b518x_VerNeSessionCancelRawEnv` on `encSession (clearPending s_old)`. -/
theorem b518x_sessDeserializeCancelEnv_of_scopeIn
    {s_old : Session (List (BitVec 8))}
    (h : CryptoVerification.SignalSession.Cli.Slots.scopeIn ⟨some s_old⟩)
    (hver : s_old.state.sessionVersion = 4#32) :
    SessDeserializeCancelEnv ⟨some (clearPending s_old)⟩
      (sessDeserEvents ⟨some (clearPending s_old)⟩) ∧
    b518x_VerNeSessionCancelRawEnv (encSession (clearPending s_old))
      (sessDeserEvents ⟨some (clearPending s_old)⟩) := by
  have hok := b518x_overPrevEncOKAt_clearPending_of_scopeIn h hver
  have hdes : SessDeserializeCancelEnv ⟨some (clearPending s_old)⟩
      (sessDeserEvents ⟨some (clearPending s_old)⟩) := ⟨hok.2.1, rfl⟩
  exact ⟨hdes, ⟨clearPending s_old, rfl, hdes⟩⟩

theorem b518x_verNeSessionCancelRawEnv_of_exact
    {enc : List (BitVec 8)} {sess : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hok : OverPrevEncOKAt enc sess)
    (hdes : SessDeserializeCancelEnv ⟨some sess⟩ evs) :
    b518x_VerNeSessionCancelRawEnv enc evs :=
  ⟨sess, hok.1, hdes⟩

theorem b518x_verNeSessionCancelEnv_of_exact
    {enc : List (BitVec 8)} {sess : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hok : OverPrevEncOKAt enc sess)
    (hrec_le : (encodeRecord ⟨some sess⟩).length ≤ deserCancelFineMaxReq)
    (hdes : SessDeserializeCancelEnv ⟨some sess⟩ evs) :
    b518x_VerNeSessionCancelEnv enc evs :=
  ⟨sess, hok.1, hrec_le, hdes⟩

theorem b518x_fitsExact_of_fitsRaw {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {sess : Session (List (BitVec 8))}
    (hok : OverPrevEncOKAt enc sess)
    (hfit : FitsEnv M lim st0 (b518x_VerNeSessionCancelRawEnv enc)) :
    FitsEnv M lim st0 (SessDeserializeCancelEnv ⟨some sess⟩) :=
  fun evs hdes => hfit evs (b518x_verNeSessionCancelRawEnv_of_exact hok hdes)

theorem b518x_fitsExact_of_fitsCapped {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {sess : Session (List (BitVec 8))}
    (hok : OverPrevEncOKAt enc sess)
    (hrec_le : (encodeRecord ⟨some sess⟩).length ≤ deserCancelFineMaxReq)
    (hfit : FitsEnv M lim st0 (b518x_VerNeSessionCancelEnv enc)) :
    FitsEnv M lim st0 (SessDeserializeCancelEnv ⟨some sess⟩) :=
  fun evs hdes => hfit evs (b518x_verNeSessionCancelEnv_of_exact hok hrec_le hdes)

theorem b518x_verNeTightTopEnvOf_of_parts
    {DecEnv : List (BitVec 8) → List AllocEvent → Prop} {enc : List (BitVec 8)}
    {evs1 evs_dec evs_free evs3 : List AllocEvent}
    (h1 : VerNeS1Env evs1) (hd : DecEnv enc evs_dec)
    (hf : FreeOnlyEvs evs_free) (h3 : VerNeTailEnv evs3) :
    b518x_VerNeTightTopEnvOf DecEnv enc (evs1 ++ (evs_dec ++ evs_free) ++ evs3) := by
  rw [List.append_assoc]
  exact Or.inr ⟨evs1, (evs_dec ++ evs_free) ++ evs3, rfl, h1,
    Or.inr ⟨evs_dec ++ evs_free, evs3, rfl,
      Or.inr ⟨evs_dec, evs_free, rfl, hd, hf⟩, h3⟩⟩

/-! ## Top-Level Block-`518` (`+0x1ee8 → +0x2620`) Exact Decode Contract -/

/-- Fixed-`ext` `[LibsignalPlacement]` exact-trace inlined `SessionStructure::decode` of
`enc = encSession sess` (`(blkPl_518).base + 0x1ee8 → (blkPl_518).base + 0x2620`, closure frame
`s.sp`) on `lsProg_518 ext` under `LibsignalCodeRoLoaded lsmpl`, tightening
`LoopDefsBudget.OverPrevDecodeCroPlacedAt` from `OverPrevDecodeEnv enc` to
`SessDeserializeCancelEnv ⟨some sess⟩`. -/
def b518x_OverPrevDecodeExactCroPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st0 : M.σ) (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8))),
    OverPrevEncOKAt enc sess →
    FitsEnv M lim st0 (SessDeserializeCancelEnv ⟨some sess⟩) →
    LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x21 = s.sp + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = prevPtr →
    s.readReg64 .x29 = s.sp + 0xc70#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        A.pool lim st0 s)
      (fun sf P_f =>
        (∃ evs, SessDeserializeCancelEnv ⟨some sess⟩ evs ∧
          (P_f ⊢ overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
              overDecScratchPostBudget A s.sp (ssgqOf sess) ∗
              stackAt s.sp overDecStackX ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ anyHeap)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False)

private theorem b518x_sessionShim_of_noAllocShim {H : String → Option (State → State)}
    {sym : String}
    (h : HookSat H sym noAllocShimBudgetSpec) :
    HookSat H sym sessionShimBudgetSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, ?_⟩
  intro x R s0 hrun hpre hal
  dsimp only [sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hpre
  have hpre' : s0.mem ⊨ noAllocShimBudgetSpec.pre () s0 ∗ R := by
    dsimp only [noAllocShimBudgetSpec]
    exact hpre
  obtain ⟨hret, hcc, hout⟩ := hsat () R s0 hrun hpre' hal
  refine ⟨hret, hcc, ?_⟩
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [noAllocShimBudgetSpec] at hpost
    dsimp only [sessionShimBudgetSpec, CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    rw [satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hpost.1.2, hpost.1.1, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp1, hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, ho2⟩))

/-! ## Exact Loop, Tag-6 (`sender_chain`), and Tag-7 (`receiver_chains`) Infrastructure -/

private inductive b518r3_FreshBytesChain : List GenFieldQ → SSGQ → Prop
  | nil (v : SSGQ) : b518r3_FreshBytesChain [] v
  | cons (fl : GenFieldQ) (fs : List GenFieldQ) (v : SSGQ) :
      GenFieldQ.FreshBytes v fl →
      b518r3_FreshBytesChain fs (v.apply fl) →
      b518r3_FreshBytesChain (fl :: fs) v

private theorem b518r3_freshBytesChain_cons_inv {fl : GenFieldQ} {fs : List GenFieldQ} {v : SSGQ}
    (h : b518r3_FreshBytesChain (fl :: fs) v) :
    GenFieldQ.FreshBytes v fl ∧ b518r3_FreshBytesChain fs (v.apply fl) := by
  cases h with
  | cons _ _ _ h1 h2 => exact ⟨h1, h2⟩

private theorem b518r3_freshBytesChain_of_getElem (fs : List GenFieldQ) (v : SSGQ)
    (h : ∀ k (hk : k < fs.length), GenFieldQ.FreshBytes ((fs.take k).foldl SSGQ.apply v) (fs[k]'hk)) :
    b518r3_FreshBytesChain fs v := by
  induction fs generalizing v with
  | nil => exact .nil v
  | cons fl fs ih =>
    refine .cons fl fs v (h 0 (Nat.zero_lt_succ _)) (ih (v.apply fl) ?_)
    intro k hk
    exact h (k + 1) (Nat.succ_lt_succ hk)

private theorem b518r3_freshBytesChain_recFieldsQ
    (r : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8))) :
    b518r3_FreshBytesChain (recFieldsQ r) SSGQ.empty :=
  b518r3_freshBytesChain_of_getElem (recFieldsQ r) SSGQ.empty
    (fun k hk => by
      have h := freshBytes_ssgqAfter r hk
      dsimp only [ssgqAfter] at h
      exact h)

private theorem b518r3_freshBytesChain_genFieldsQ (s : Session (List (BitVec 8))) :
    b518r3_FreshBytesChain (genFieldsQ s) SSGQ.empty := by
  have h := b518r3_freshBytesChain_recFieldsQ ⟨some s⟩
  dsimp only [recFieldsQ] at h
  exact h

private def b518r3_NonEmptyPq : GenFieldQ → Prop
  | .pq bs => bs ≠ []
  | _ => True

private theorem b518r3_nonEmptyPq_genFieldsQ (s : Session (List (BitVec 8))) :
    ∀ fl ∈ genFieldsQ s, b518r3_NonEmptyPq fl := by
  intro fl hfl
  unfold genFieldsQ at hfl
  rw [List.mem_append] at hfl
  rcases hfl with hmap | hpq
  · rw [List.mem_map] at hmap
    rcases hmap with ⟨fx, hfx, rfl⟩
    have hnp := noPq_of_mem_genFieldsX rfl hfx
    cases fx with
    | pq _ => exact False.elim hnp
    | _ => trivial
  · split_ifs at hpq with heq
    · cases hpq
    · rw [List.mem_singleton] at hpq
      subst hpq
      exact heq

private theorem b518r3_apply_recv_len (v : SSGQ) (fl : GenFieldQ) :
    (v.apply fl).base.recv.length =
      (match fl with | .base (.recv _) => v.base.recv.length + 1 | _ => v.base.recv.length) := by
  cases fl with
  | base f => cases f <;> simp [SSGQ.apply, SSG.apply]
  | _ => rfl

private theorem b518r3_lt5_cases {n : Nat} (h : n < maxReceiverChains) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by
  have h5 : maxReceiverChains = 5 := rfl
  omega

private theorem b518r3_vecCap4_toNat {n : Nat} (h : n < maxReceiverChains) :
    (BitVec.ofNat 64 (vecCap4Of n)).toNat = vecCap4Of n := by
  rcases b518r3_lt5_cases h with rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem b518r3_vecCap4_bounds {n : Nat} (h : n < maxReceiverChains) :
    n ≤ (BitVec.ofNat 64 (vecCap4Of n)).toNat ∧
      (BitVec.ofNat 64 (vecCap4Of n)).toNat * 104 < 2 ^ 63 := by
  rcases b518r3_lt5_cases h with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem b518r3_vecCap4_full_next {n : Nat} (h : n < maxReceiverChains)
    (hfull : n = vecCap4Of n) :
    BitVec.ofNat 64 (max (2 * (BitVec.ofNat 64 (vecCap4Of n)).toNat) 4) =
      BitVec.ofNat 64 (vecCap4Of (n + 1)) ∧
    n < (BitVec.ofNat 64 (vecCap4Of (n + 1))).toNat ∧
    (BitVec.ofNat 64 (vecCap4Of (n + 1))).toNat * 104 < 2 ^ 63 ∧
    8 + max (2 * (BitVec.ofNat 64 (vecCap4Of n)).toNat) 4 * 104 ≤ 2 ^ 63 := by
  rcases b518r3_lt5_cases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨rfl, by decide, by decide, by decide⟩
  · cases hfull
  · cases hfull
  · cases hfull
  · exact ⟨rfl, by decide, by decide, by decide⟩

private theorem b518r3_growEvents_eq {n : Nat} (h : n < maxReceiverChains)
    (hfull : n = vecCap4Of n) :
    growOne104Events (BitVec.ofNat 64 (vecCap4Of n)) = vec104GrowEvents (vecCap4Of n) := by
  rcases b518r3_lt5_cases h with rfl | rfl | rfl | rfl | rfl
  · rfl
  · cases hfull
  · cases hfull
  · cases hfull
  · rfl

private theorem b518r3_vecCap4_not_full {n : Nat} (h : n < maxReceiverChains)
    (hne : ¬ n = vecCap4Of n) :
    n < (BitVec.ofNat 64 (vecCap4Of n)).toNat ∧ vecCap4Of (n + 1) = vecCap4Of n := by
  rcases b518r3_lt5_cases h with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩
  · exact absurd rfl hne

private def b518r3_chainRestCap (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  b518x_vecU8Fresh0 A ss v.base.lik ∗
    b518x_vecU8Fresh0 A (ss + 0x18#64) v.base.rik ∗
    b518x_vecU8Fresh0 A (ss + 0x30#64) v.base.root ∗
    (∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAt A a c)
        (ss + 0x48#64) (BitVec.ofNat 64 (vecCap4Of v.base.recv.length)) ptrRecv v.base.recv) ∗
    b518x_vecU8Fresh0 A (ss + 0x60#64) v.ext.abk ∗
    b518x_vecU8Fresh0 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

private theorem b518r3_prostSSGQAtCap_sender_none (A : RustAlloc) (ss : BitVec 64) (v : SSGQ)
    (hnone : v.base.sender = none) :
    b518x_prostSSGQAtCap A ss v =
      ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96 ∗
        b518r3_chainRestCap A ss v := by
  unfold b518x_prostSSGQAtCap b518r3_chainRestCap
  rw [hnone]
  cases v.base.pending <;> (dsimp only; sep_ac_rfl)

private theorem b518r3_prostSSGQAtCap_sender_some (A : RustAlloc) (ss : BitVec 64) (v : SSGQ)
    (c : ChainG) :
    b518x_prostSSGQAtCap A ss (v.apply (.base (.sender c))) =
      prostChainGAt A (ss + 0x90#64) c ∗ b518r3_chainRestCap A ss v := by
  rcases v with ⟨⟨ver, lik, rik, root, prevCounter, recv, sender, pending⟩, ext⟩
  unfold b518x_prostSSGQAtCap b518r3_chainRestCap SSGQ.apply SSG.apply
  cases pending <;> (dsimp only; sep_ac_rfl)

private def b518r3_senderFrameRestCap (A : RustAlloc) (g : OverDecG) (v : SSGQ)
    (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    b518r3_chainRestCap A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX)

private theorem b518r3_overDecHeapCap_sender_pre {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) (hnone : v.base.sender = none) :
    b518x_overDecHeapCap A lim st s g (c.payload ++ rest) v =
      ((g.q + 0x9c0#64) ↦₆₄ noneCap) ∗ memRegion (g.q + 0x9c8#64) 96 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        A.pool lim st s ∗ stackAt g.q chainMerge3StackX ∗
        b518r3_senderFrameRestCap A.repAlloc g v (c.payload ++ rest).length := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  have h98 : g.q + 0x930#64 + 0x98#64 = g.q + 0x9c8#64 := by rw [BitVec.add_assoc]; rfl
  unfold b518x_overDecHeapCap overPrevElemRestBudget b518r3_senderFrameRestCap
  rw [b518r3_prostSSGQAtCap_sender_none A.repAlloc (g.q + 0x930#64) v hnone,
      h90, h98,
      sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

private theorem b518r3_overDecHeapCap_sender_post {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt A.repAlloc (g.q + 0x9c0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      A.pool lim st s ∗
      stackAt g.q chainMerge3StackX ∗
      b518r3_senderFrameRestCap A.repAlloc g v (c.payload ++ rest).length =
    b518x_overDecHeapCap A lim st s g rest (v.apply (.base (.sender c))) := by
  have h90 : g.q + 0x930#64 + 0x90#64 = g.q + 0x9c0#64 := by rw [BitVec.add_assoc]; rfl
  unfold b518x_overDecHeapCap overPrevElemRestBudget b518r3_senderFrameRestCap
  rw [b518r3_prostSSGQAtCap_sender_some A.repAlloc (g.q + 0x930#64) v c, h90,
      ← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

set_option maxHeartbeats 600000 in
private theorem b518r3_armSender_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hC5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEvents M lim st (chainMergeEvents c))
    (hregs : OverDecRegsCroPlaced ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCap A lim st s g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim (M.stepEvents (chainMergeEvents c) st) sf g rest
          (v.apply (.base (.sender c)))))
      (fun _ _ => False) := by
  rcases hregs with ⟨hcro, hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  have hpay_eq : (GenFieldQ.base (.sender c)).payload = c.payload := rfl
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDecChain_payload_suffix hsuf hlen
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := ⟨pfx, hpfx.symm⟩
  rw [hpay_eq, b518r3_overDecHeapCap_sender_pre A lim st s g v hsuf_pay hnone,
      overDecChain_mem96 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u7 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 => ?_
  have hstepA :=
    overDecChain_segA_placed_budget A lim st ext s g.q u1 u2 u3 u4 u5 u6 u7 u8 u9
      hpc hrun hsp hal hx0 hx21 hx24 hx25 hx29
  refine SepWPp_bind_sepWP_frame_cro hcro hstepA (by sep_focus)
    fun s1 hpc1 hrun1 _hcl1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  refine SepWPp_weaken_frame (b518x_overDecChain_bridge_ext A.repAlloc g.q)
    (by sep_focus) ?_
  have hsp1q : s1.sp = g.q := hsp1.trans hsp
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hal]
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  let xGhost : ChainMergeGenGhost :=
    ⟨g.q + 0x9c0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length), rest⟩
  refine SepWPp_call_frame_cro_noPanic
    (x := (xGhost, st))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0x9c0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents c))
    (T := b518x_chain3GAtCap A.repAlloc (g.q + 0x9c0#64) 0 ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) ∗
      A.pool lim st s1 ∗
      stackAt g.q chainMerge3StackX)
    hcro1 hC5 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [b518x_chainMerge3ExactSpecW', xGhost]; rw [hsp1q])
    ⟨hx0_w8, hx1_1, hx2_1, hcok, hpay_len, hfit⟩
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hcl2 _hcro2 => ?_)
  dsimp only [b518x_chainMerge3ExactSpecW', xGhost]
  rw [hsp1q, sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨htr2_1, hx0_2⟩
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1q
  have htr2 : s2.trace = s0.trace := htr2_1.trans (htr1.trans htr)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hstepB :=
    overDecChain_segB_placed_budget A lim (M.stepEvents (chainMergeEvents c) st) ext s2
      g.q g.r19 g.r20 g.r26 g.prevPtr
      hpc2 hrun2 hsp2 hx0_2
      ((hx19_cs.trans hx19_1).trans hx19) ((hx20_cs.trans hx20_1).trans hx20)
      ((hx21_cs.trans hx21_1).trans hx21) ((hx24_cs.trans hx24_1).trans hx24)
      ((hx25_cs.trans hx25_1).trans hx25) ((hx26_cs.trans hx26_1).trans hx26)
      ((hx27_cs.trans hx27_1).trans hx27) ((hx28_cs.trans hx28_1).trans hx28)
      ((hx29_cs.trans hx29_1).trans hx29)
  refine SepWPp_ret_sepWP_frame hstepB (by sep_focus)
    fun sf hpcf hrunf hclf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    ((hvregs_f.trans hvregs_cs).trans hvregs_1).trans hvregs⟩, ?_⟩
  rw [← b518r3_overDecHeapCap_sender_post A lim (M.stepEvents (chainMergeEvents c) st) sf g v hsuf_pay]
  exact Entails.of_eq (by sep_ac_rfl)

private def b518r3_prostSSGQRestCap (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  b518x_vecU8Fresh0 A ss v.base.lik ∗
    b518x_vecU8Fresh0 A (ss + 0x18#64) v.base.rik ∗
    b518x_vecU8Fresh0 A (ss + 0x30#64) v.base.root ∗
    b518x_vecU8Fresh0 A (ss + 0x60#64) v.ext.abk ∗
    b518x_vecU8Fresh0 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

private theorem b518r3_prostSSGQAtCap_eq_recv_sep_rest (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    b518x_prostSSGQAtCap A ss v =
      (∃∗ ptrRecv : BitVec 64,
        vecAt A 104 8 (fun c a => prostChainGAt A a c)
          (ss + 0x48#64) (BitVec.ofNat 64 (vecCap4Of v.base.recv.length)) ptrRecv v.base.recv) ∗
        b518r3_prostSSGQRestCap A ss v := by
  unfold b518x_prostSSGQAtCap b518r3_prostSSGQRestCap
  sep_ac_rfl

private theorem b518r3_prostSSGQRestCap_apply_recv (A : RustAlloc) (ss : BitVec 64) (v : SSGQ)
    (c : ChainG) :
    b518r3_prostSSGQRestCap A ss (v.apply (.base (.recv c))) =
      b518r3_prostSSGQRestCap A ss v :=
  rfl

private def b518r3_recvFrameRestCap (A : RustAlloc) (g : OverDecG) (v : SSGQ)
    (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    b518x_prostSSGQAtCap A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX)

private def b518r3_recvPostMergeHeapCap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) (c : ChainG) : SepProp :=
  overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    b518x_prostSSGQAtCap A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

private theorem b518r3_overDecHeapCap_eq_recv_split {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    b518x_overDecHeapCap A lim st s g (c.payload ++ rest) v =
      (memRegion (g.q + 0xbf0#64) 80 ∗ A.pool lim st s) ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        stackAt g.q chainMerge3StackX ∗
        b518r3_recvFrameRestCap A.repAlloc g v (c.payload ++ rest).length) := by
  unfold b518x_overDecHeapCap overPrevElemRestBudget b518r3_recvFrameRestCap
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

private theorem b518r3_recvPostMergeHeapCap_eq_unsplit {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      A.pool lim st s ∗
      stackAt g.q chainMerge3StackX ∗
      b518r3_recvFrameRestCap A.repAlloc g v (c.payload ++ rest).length =
    b518r3_recvPostMergeHeapCap A lim st s g rest v c := by
  unfold b518r3_recvPostMergeHeapCap b518r3_recvFrameRestCap
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

private theorem b518r3_vecAt_recv_open_cap (A : RustAlloc) (q cap : BitVec 64)
    (cs : List ChainG) :
    (∃∗ ptr : BitVec 64,
      vecAt A 104 8 (fun c a => prostChainGAt A a c) ((q + 0x930#64) + 0x48#64) cap ptr cs) ⊢
      ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right ptr ?_
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e48, e50, e58, h0]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 400000 in
private theorem b518r3_growOne_post_cap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (q cap ptr : BitVec 64)
    (cs : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = q)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    let cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    (growOneChainSpecX M A lim).post ((q + 0x978#64, cap, ptr, bs), st) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap') ∗ ((q + 0x980#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        A.pool lim (M.stepEvents (growOne104Events cap) st) sf ∗
        stackAt q growOneChainStackX := by
  intro cap'
  unfold growOneChainSpecX growOne104SpecX
  dsimp only
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  set newCap : Nat := max (2 * cap.toNat) 4
  have h5 : maxReceiverChains = 5 := rfl
  have hcap'_toNat : cap'.toNat = newCap := by
    dsimp only [cap', newCap]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt_cap' : cs.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  refine Entails.sepExists_right p' ?_
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hsp, h0]
  change _ ⊢ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ stackAt q (464 + finishGrowStackX)
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hlt_cap', hcap'_lt, hp'⟩ ?_
  have hlive_eq : A.live p' (newCap * 104) 8 = A.live p' (cap'.toNat * 104) 8 := by
    rw [hcap'_toNat]
  have hrem : (newCap - cap.toNat) * 104 =
      104 + (cap'.toNat - (cs.length + 1)) * 104 := by
    have : newCap - cap.toNat = 1 + (cap'.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbs_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (cs.length * 104) := by
    rw [hbs, hfull]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      p' + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hlive_eq, hbs_eq, hrem,
      memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 400000 in
private theorem b518r3_vecAt_recv_push_fold_cap (A : RustAlloc) (q cap ptr : BitVec 64)
    (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
        ((cap.toNat - (cs.length + 1)) * 104) ⊢
    ∃∗ ptrRecv : BitVec 64,
      vecAt A 104 8 (fun c' a => prostChainGAt A a c')
        ((q + 0x930#64) + 0x48#64) cap ptrRecv (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  unfold vecAt vecHeader vecBuf
  refine Entails.sepExists_right ptr ?_
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := by
    rw [BitVec.ofNat_add]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e48, e50, e58, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]
  simp only [hne0, ↓reduceIte]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (A.live ptr (cap.toNat * 104) 8 ∗
            (arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
              prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
            memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
              ((cap.toNat - (cs.length + 1)) * 104))) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
          ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          A.live ptr (cap.toNat * 104) 8 ∗
          arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
          prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) := by
    sep_ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

private theorem b518r3_prostSSGQAtCap_fold_apply_recv (A : RustAlloc) (q cap ptr : BitVec 64)
    (v : SSGQ) (c : ChainG)
    (hcap_eq : cap = BitVec.ofNat 64 (vecCap4Of (v.base.recv.length + 1)))
    (hlt : v.base.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
        ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
      b518r3_prostSSGQRestCap A (q + 0x930#64) v) ⊢
    b518x_prostSSGQAtCap A (q + 0x930#64) (v.apply (.base (.recv c))) := by
  rw [b518r3_prostSSGQAtCap_eq_recv_sep_rest A (q + 0x930#64) (v.apply (.base (.recv c))),
      b518r3_prostSSGQRestCap_apply_recv A (q + 0x930#64) v c]
  have hlen_app : ((v.apply (.base (.recv c))).base.recv).length = v.base.recv.length + 1 := by
    dsimp only [SSGQ.apply, SSG.apply]
    simp
  rw [hlen_app, ← hcap_eq]
  dsimp only [SSGQ.apply, SSG.apply]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
        prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
        b518r3_prostSSGQRestCap A (q + 0x930#64) v) =
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
        prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104)) ∗
      b518r3_prostSSGQRestCap A (q + 0x930#64) v := by
    sep_ac_rfl
  rw [hgrp]
  exact sepConj_mono_left
    (b518r3_vecAt_recv_push_fold_cap A q cap ptr v.base.recv c hlt hcap_lt hptr)

private def b518r3_recv2114HeapCap {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ)
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp) :
    SepProp :=
  overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    ((g.q + 0x980#64) ↦₆₄ ptr') ∗
    ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64) 104 ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    b518r3_prostSSGQRestCap A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

set_option maxHeartbeats 800000 in
private theorem b518r3_step_2114_to_2160_cap [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp)
    {Qp : State → SepProp → Prop}
    (hcap_eq : cap' = BitVec.ofNat 64 (vecCap4Of (v.base.recv.length + 1)))
    (hlt : v.base.recv.length < cap'.toNat)
    (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    (hmov_c : ∀ b : BitVec 64,
      (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ⊢ prostChainGAt A.repAlloc b c)
    (hregs : OverDecRegsPlaced ext s0 g 0x2114#64 s)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 v.base.recv.length) :
    SepWPp (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s
      (b518r3_recv2114HeapCap A lim st s g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim st sf g rest (v.apply (.base (.recv c)))))
      Qp := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64
  let F_2114 : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    b518r3_prostSSGQRestCap A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX
  have hsplit : b518r3_recv2114HeapCap A lim st s g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c =
      (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
       ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
       ∃∗ dw6 : BitVec 64,
        ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
        chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6 ∗
        A.pool lim st s) ∗ F_2114 := by
    unfold b518r3_recv2114HeapCap F_2114
    rw [show ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64 = dst from rfl,
        memRegion104_eq_exists_chunks104_6QWAt_rc dst]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply congrArg sepExists; funext _)
    sep_ac_rfl
  rw [hsplit]
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  have hstep := step_2114_to_2160_placed_budget A lim st ext s g ptr'
    (BitVec.ofNat 64 v.base.recv.length) (BitVec.ofNat 64 v.base.recv.length)
    q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
    hpc hrun hsp hal hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame hstep rfl
    fun sf hpcf hrunf hCLf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hCLf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  have hc_dst := hmov_c dst
  have hss := b518r3_prostSSGQAtCap_fold_apply_recv A.repAlloc g.q cap' ptr' v c
    hcap_eq hlt hcap_lt hptr
  simp only [A.repAlloc_live_norm] at hss
  have ha90 := memRegion344_a90_join_rc g.q q0 q1 q2 q3 q4 q5 w6
  let F_keep : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st sf
  have h1 :
      (((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗
        A.pool lim st sf) ∗ F_2114 ⊢
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
        prostChainGAt A.repAlloc dst c ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        b518r3_prostSSGQRestCap A.repAlloc (g.q + 0x930#64) v) ∗
      (chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        memRegion (g.q + 0xaf8#64) 240) ∗
      F_keep := by
    refine Entails.trans (Q := (chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ∗
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        b518r3_prostSSGQRestCap A.repAlloc (g.q + 0x930#64) v ∗
        (chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          memRegion (g.q + 0xaf8#64) 240) ∗
        F_keep))
      (Entails.of_eq (by unfold F_2114 F_keep; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hc_dst) (Entails.of_eq (by sep_ac_rfl))
  refine Entails.trans h1 ?_
  refine Entails.trans (sepConj_mono hss (sepConj_mono ha90 (Entails.refl F_keep))) ?_
  exact Entails.of_eq (by unfold b518x_overDecHeapCap overPrevElemRestBudget F_keep; sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem b518r3_recvSegB [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hFresh : (GenFieldQ.base (.recv c)).Fresh v)
    (hfit : FitsEvents M lim st
      (if v.base.recv.length = vecCap4Of v.base.recv.length
       then vec104GrowEvents (vecCap4Of v.base.recv.length) else []))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : OverDecRegsPlaced ext s0 g 0x2310#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (b518r3_recvPostMergeHeapCap A lim st s g rest v c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim
          (M.stepEvents
            (if v.base.recv.length = vecCap4Of v.base.recv.length
             then vec104GrowEvents (vecCap4Of v.base.recv.length) else []) st)
          sf g rest (v.apply (.base (.recv c)))))
      (fun _ _ => False) := by
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  set cap : BitVec 64 := BitVec.ofNat 64 (vecCap4Of v.base.recv.length)
  have hcap_toNat : cap.toNat = vecCap4Of v.base.recv.length := b518r3_vecCap4_toNat hfresh
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold b518r3_recvPostMergeHeapCap
  rw [b518r3_prostSSGQAtCap_eq_recv_sep_rest A.repAlloc (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame (b518r3_vecAt_recv_open_cap A.repAlloc g.q cap v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨_hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame (prostChainGAt_move_chunks104_rc A.repAlloc (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull_nat : v.base.recv.length = vecCap4Of v.base.recv.length
  · have hfull : v.base.recv.length = cap.toNat := hfull_nat.trans hcap_toNat.symm
    obtain ⟨hcap_next, _, _, hmax_lt⟩ := b518r3_vecCap4_full_next hfresh hfull_nat
    have hite_full :
        (if v.base.recv.length = vecCap4Of v.base.recv.length
         then vec104GrowEvents (vecCap4Of v.base.recv.length) else []) =
          vec104GrowEvents (vecCap4Of v.base.recv.length) := by
      split_ifs; rfl
    have hgrow_eq : growOne104Events cap = vec104GrowEvents (vecCap4Of v.base.recv.length) :=
      b518r3_growEvents_eq hfresh hfull_nat
    have hfit_evs : FitsEvents M lim st (growOne104Events cap) := by
      rw [hgrow_eq, ← hite_full]
      exact hfit
    have hfit_grow : FitsEnv M lim st (GrowOne104Env cap) := fun _ hevs => hevs ▸ hfit_evs
    refine SepWPp_weaken_frame (vecBuf_recv_full_open_rc_ext A.repAlloc cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    simp only [A.repAlloc_live_norm]
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed_budget A lim st ext s g cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_cro hcro hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 _hCLs1 hcro1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
    refine SepWPp_weaken_frame (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_cro_noPanic
      (x := ((g.q + 0x978#64, cap, ptr, bs), st))
      hcro1 hGrow hpcs1 hruns1 hals1 hlrs1
      (growOne_plain_pre_eq_q_ext A lim st g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt, hfit_grow⟩
      (by sep_focus)
      (hnext := fun sm hpcm hrunm hspm _halm hcsm _hCLm _hcrom => ?_)
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame
      (b518r3_growOne_post_cap A lim st g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    set cap' : BitVec 64 := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
    refine SepWPp_weaken_frame (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed_budget A lim (M.stepEvents (growOne104Events cap) st) ext sm g cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame hstep2 (by sep_focus)
      fun s2 hpcs2 hruns2 hCLs2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hCLs2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame
      (P₂ := b518r3_recv2114HeapCap A lim
        (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
        s2 g rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · unfold b518r3_recv2114HeapCap
      rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
      sep_ac_rfl
    · rw [sepConj_emp]
      refine overDec_sepWPp_mono_post ?_
        (b518r3_step_2114_to_2160_cap A lim
          (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
          ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
          hcap_next hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2)
      rintro sf P_f - - ⟨hregsf, hentf⟩
      refine ⟨hregsf, ?_⟩
      rw [hite_full, ← hgrow_eq, ← hlen_cap]
      exact hentf
  · obtain ⟨hlt, hcap_same⟩ := b518r3_vecCap4_not_full hfresh hfull_nat
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A.repAlloc cap ptr v.base.recv hlt hcap_lt]
    simp only [A.repAlloc_live_norm]
    have hstep1 := step_2310_to_2114_of_ne_placed_budget A lim st ext s g cap
      (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hCLs1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame
      (P₂ := b518r3_recv2114HeapCap A lim st s1 g rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by unfold b518r3_recv2114HeapCap; sep_ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    have hcap_eq_next : cap = BitVec.ofNat 64 (vecCap4Of (v.base.recv.length + 1)) := by
      rw [hcap_same]
    refine overDec_sepWPp_mono_post ?_
      (b518r3_step_2114_to_2160_cap A lim st ext s0 s1 g v c rest cap ptr
        q0 q1 q2 q3 q4 q5 w6 H_c hcap_eq_next hlt hcap_lt hptr hmov_c hregs1 hx22s1)
    rintro sf P_f - - ⟨hregsf, hentf⟩
    refine ⟨hregsf, ?_⟩
    have hite_not :
        (if v.base.recv.length = vecCap4Of v.base.recv.length
         then vec104GrowEvents (vecCap4Of v.base.recv.length) else []) = [] := by
      split_ifs; rfl
    rw [hite_not, M.stepEvents_nil]
    exact hentf

private theorem b518r3_subroutine_ok_cro_of_cl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCl lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCl]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem b518r3_recv_cells_pool_reassoc
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 pool m24 restF : SepProp) :
    (c0 ∗ c1 ∗ c2 ∗ c3 ∗ c4 ∗ c5 ∗ c6 ∗ c7 ∗ c8 ∗ c9 ∗ pool) ∗ (m24 ∗ restF) =
      ((c0 ∗ c1 ∗ c2 ∗ c3 ∗ c4 ∗ c5 ∗ c6 ∗ c7 ∗ c8 ∗ c9) ∗ m24) ∗ (pool ∗ restF) := by
  sep_ac_rfl

private theorem b518r3_recv_call_frame_reassoc (ch pool hbe8 cur stk restF : SepProp) :
    ch ∗ (pool ∗ (hbe8 ∗ cur ∗ stk ∗ restF)) = (ch ∗ hbe8 ∗ cur ∗ pool ∗ stk) ∗ restF := by
  sep_ac_rfl

set_option maxHeartbeats 600000 in
private theorem b518r3_armRecv_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (withLsCodeRoLoaded lsmpl (growOneChainSpecX M A lim)))
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext)
    (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hok : (GenFieldQ.base (.recv c)).Ok)
    (hfresh : (GenFieldQ.base (.recv c)).Fresh v)
    (hsuf : ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEvents M lim st
      (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.base (.recv c))))
    (hregs_cro : OverDecRegsCroPlaced ext s0 g 0x22e0#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (b518x_overDecHeapCap A lim st s g ((GenFieldQ.base (.recv c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim
          (M.stepEvents
            (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length (.base (.recv c)))
            st)
          sf g rest (v.apply (.base (.recv c)))))
      (fun _ _ => False) := by
  rcases hregs_cro with ⟨hcro, hregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  have hfit_split : FitsEvents M lim st (chainMergeEvents c) ∧
      FitsEvents M lim (M.stepEvents (chainMergeEvents c) st)
        (if v.base.recv.length = vecCap4Of v.base.recv.length
         then vec104GrowEvents (vecCap4Of v.base.recv.length) else []) := by
    dsimp only [mergeFieldQEvents] at hfit
    exact (fitsEvents_append M lim _ _ st).mp hfit
  rw [hpay_eq, b518r3_overDecHeapCap_eq_recv_split A lim st s g v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hsaved : OverDecSavedRegs (toChain3GTop g) s :=
    ⟨hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hstep := overDecRecv_pre_step_80_placed_budget A lim st (ext := ext) (g := toChain3GTop g)
    hpc hrun hsp hsp_align htr hsaved hx0
  refine SepWPp_bind_sepWP_frame_cro hcro hstep rfl
    fun s1 hpc1 hrun1 _hCL1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  dsimp only [toChain3GTop] at hsp1 hx1_1 hx2_1 ⊢
  refine SepWPp_weaken_frame (b518x_default_cells_bf0_entail_chain3GAtCap_ext A.repAlloc g.q)
    (b518r3_recv_cells_pool_reassoc _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hq_align]
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  let xGhost : ChainMergeGenGhost :=
    ⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length), rest⟩
  refine SepWPp_call_frame_cro_noPanic
    (x := (xGhost, st))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62 ∧
      FitsEvents M lim st (chainMergeEvents c))
    (T := b518x_chain3GAtCap A.repAlloc (g.q + 0xbf0#64) 0 ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) ∗
      A.pool lim st s1 ∗
      stackAt g.q chainMerge3StackX)
    (F := b518r3_recvFrameRestCap A.repAlloc g v (c.payload ++ rest).length)
    hcro1 hChain5 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [b518x_chainMerge3ExactSpecW', xGhost]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay, hfit_split.1⟩
    (b518r3_recv_call_frame_reassoc _ _ _ _ _ _)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hCL2 hcro2 => ?_)
  dsimp only [b518x_chainMerge3ExactSpecW']
  rw [hsp1, sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨htr2_1, hx0_2⟩
  dsimp only [xGhost]
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  rcases hsaved1 with ⟨hx19_1, hx20_1, hx26_1, hx21_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hCL2,
     hx19_cs.trans hx19_1, hx20_cs.trans hx20_1, hx26_cs.trans hx26_1,
     hx21_cs.trans hx21_1, hx24_cs.trans hx24_1, hx25_cs.trans hx25_1,
     hx27_cs.trans hx27_1, hx28_cs.trans hx28_1, hx29_cs.trans hx29_1,
     hvregs_cs.trans hvregs_1⟩
  have hpost_eq :
      (prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) rest ∗
        A.pool lim (M.stepEvents (chainMergeEvents c) st) s2 ∗
        stackAt g.q chainMerge3StackX) ∗
      b518r3_recvFrameRestCap A.repAlloc g v (c.payload ++ rest).length =
      b518r3_recvPostMergeHeapCap A lim (M.stepEvents (chainMergeEvents c) st) s2 g rest v c := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact b518r3_recvPostMergeHeapCap_eq_unsplit A lim (M.stepEvents (chainMergeEvents c) st) s2 g v hsuf_pay
  rw [hpost_eq]
  refine overDec_sepWPp_mono_post ?_
    (b518r3_recvSegB hGrow (M.stepEvents (chainMergeEvents c) st) s0 s2 g v c rest
      hfresh hfit_split.2 hcro2 hregs2 hx0_2)
  rintro sf P_f - - ⟨hregsf, hentf⟩
  refine ⟨hregsf, ?_⟩
  dsimp only [mergeFieldQEvents]
  rw [M.stepEvents_append]
  exact hentf

private def b518r3_EntryCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG),
    g.enc ≠ [] → g.enc.length < 2 ^ 62 →
    LibsignalCodeRoLoaded lsmpl s.mem →
    (lsProg_518 ext).CodeLoaded s.mem →
    s.pc = (blkPl_518).base + 0x1ee8#64 →
    s.status = .Running →
    s.sp = g.q →
    (s.sp &&& 15#64 == 0#64) = true →
    s.trace = s0.trace →
    s.readReg64 .x19 = g.r19 →
    s.readReg64 .x20 = g.r20 →
    s.readReg64 .x26 = g.r26 →
    s.readReg64 .x21 = g.q + 0x930#64 →
    s.readReg64 .x24 = 1#64 →
    s.readReg64 .x25 = 0xffffffffffffffff#64 →
    s.readReg64 .x27 = g.prevPtr →
    s.readReg64 .x29 = g.q + 0xc70#64 →
    calleeSavedVRegs s = calleeSavedVRegs g.sv →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (overPrevElemAtBudget A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        overDecScratchPre g.q ∗ stackAt g.q overDecStackX ∗ A.pool lim st s)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim st sf g g.enc SSGQ.empty))
      (fun _ _ => False)

private def b518r3_HeadConsCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (rest : List (BitVec 8)),
    rest ≠ [] → rest <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (b518x_overDecHeapCap A lim st s g rest v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x216c#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim st sf g rest v))
      (fun _ _ => False)

private def b518r3_HeadNilCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ),
    g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x2160#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) s
      (b518x_overDecHeapCap A lim st s g [] v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim st sf g [] v))
      (fun _ _ => False)

private def b518r3_KeyCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    OverDecAnyField fl → fl.Ok → (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + overDecArmOff fl) s
      (b518x_overDecHeapCap A lim st s g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) sf ∧
        sf.readReg64 .x0 = overDecWt fl ∧
        (P_f ⊢ b518x_overDecHeapCap A lim st sf g (fl.payload ++ rest) v))
      (fun _ _ => False)

private def b518r3_ArmCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (P : GenFieldQ → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v → GenFieldQ.FreshBytes v fl → b518r3_NonEmptyPq fl →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    FitsEvents M lim st
      (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) →
    OverDecRegsCroPlaced ext s0 g (overDecArmOff fl) s →
    s.readReg64 .x0 = overDecWt fl →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCap A lim st s g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          sf g rest (v.apply fl)))
      (fun _ _ => False)

private def b518r3_FieldCro [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (P : GenFieldQ → Prop) : Prop :=
  ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
    P fl → fl.Ok → fl.Fresh v → GenFieldQ.FreshBytes v fl → b518r3_NonEmptyPq fl →
    (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
    FitsEvents M lim st
      (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) →
    OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (b518x_overDecHeapCap A lim st s g (fl.enc ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          sf g rest (v.apply fl)))
      (fun _ _ => False)

private theorem b518r3_armSender [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hC5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext) :
    b518r3_ArmCro A lim ext OverDecSenderField := by
  intro st s0 s g v fl rest hP hok hfresh _hfb _hpq hsuf hlen hfit hregs hx0
  cases fl with
  | base f =>
    cases f with
    | sender c =>
      have hok' : c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = [] := hok
      have hfresh' : v.ext = ExtraGQ.empty ∧ v.base.sender = none := hfresh
      exact b518r3_armSender_core ext hC5 st s0 s g v c rest
        hok'.1 hfresh'.2 hsuf hlen hfit hregs hx0
    | _ => exact False.elim hP
  | _ => exact False.elim hP

private theorem b518r3_armRecv [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext) :
    b518r3_ArmCro A lim ext OverDecRecvField := by
  intro st s0 s g v fl rest hfl hok hfresh _hfb _hpq hsuf hlen hfit hregs hx0
  have hGrow := b518r3_subroutine_ok_cro_of_cl
    (growOneChain_placed_ok_cl (callerProg := lsProg_518 ext) (growOneChain_placed_ok_x hAlloc))
  cases fl with
  | base bf =>
    cases bf with
    | recv c =>
      exact b518r3_armRecv_core ext hGrow hChain5 st s0 s g v c rest
        hok hfresh hsuf hlen hfit hregs hx0
    | _ => exact False.elim hfl
  | _ => exact False.elim hfl

private theorem b518r3_field_of_key_arm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {P : GenFieldQ → Prop}
    (hK : b518r3_KeyCro A lim ext)
    (hA : b518r3_ArmCro A lim ext P)
    (hPA : ∀ fl, P fl → OverDecAnyField fl) :
    b518r3_FieldCro A lim ext P := by
  intro st s0 s g v fl rest hP hok hfr hfb hpq hsuf hlen hfit hregs
  refine overDec_sepWPp_seq (hK st s0 s g v fl rest (hPA fl hP) hok hsuf hlen hregs) ?_
  rintro sm Pm - - ⟨hregs', hx0, hent⟩
  exact overDec_sepWPp_weaken_pre hent
    (hA st s0 sm g v fl rest hP hok hfr hfb hpq hsuf hlen hfit hregs' hx0)

private theorem b518r3_arm_any [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hV : b518r3_ArmCro A lim ext OverDecVarintField)
    (hB : b518r3_ArmCro A lim ext OverDecBytesField)
    (hS : b518r3_ArmCro A lim ext OverDecSenderField)
    (hR : b518r3_ArmCro A lim ext OverDecRecvField) :
    b518r3_ArmCro A lim ext OverDecAnyField := by
  intro st s0 s g v fl rest hP
  rcases hP with h | h | h | h
  · exact hV st s0 s g v fl rest h
  · exact hB st s0 s g v fl rest h
  · exact hS st s0 s g v fl rest h
  · exact hR st s0 s g v fl rest h

private theorem b518r3_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hField : b518r3_FieldCro A lim ext OverDecAnyField)
    (hCons : b518r3_HeadConsCro A lim ext)
    (hNil : b518r3_HeadNilCro A lim ext)
    (s0 : State) (g : OverDecG) (hlen : g.enc.length < 2 ^ 62) :
    ∀ (fs : List GenFieldQ) (st : M.σ) (v : SSGQ) (s : State), fs ≠ [] →
      (∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok ∧ b518r3_NonEmptyPq fl) →
      OverDecFreshChain fs v →
      b518r3_FreshBytesChain fs v →
      fs.flatMap GenFieldQ.enc <:+ g.enc →
      FitsEvents M lim st (fieldsEventsAux (vecCap4Of v.base.recv.length) v.base.recv.length fs) →
      OverDecRegsCroPlaced ext s0 g 0x216c#64 s →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) s
        (b518x_overDecHeapCap A lim st s g (fs.flatMap GenFieldQ.enc) v)
        (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2620#64 sf ∧
          (P_f ⊢ b518x_overDecHeapCap A lim
            (M.stepEvents
              (fieldsEventsAux (vecCap4Of v.base.recv.length) v.base.recv.length fs) st)
            sf g [] (fs.foldl SSGQ.apply v)))
        (fun _ _ => False) := by
  intro fs
  induction fs with
  | nil => intro st v s hne; exact absurd rfl hne
  | cons fl fs ih =>
    intro st v s _ hmem hfr hfb hsuf hfit hregs
    obtain ⟨hany, hok, hpq⟩ := hmem fl (List.mem_cons_self ..)
    obtain ⟨hfr1, hfr2⟩ := overDecFreshChain_cons_inv hfr
    obtain ⟨hfb1, hfb2⟩ := b518r3_freshBytesChain_cons_inv hfb
    rw [overDec_flatMap_cons] at hsuf ⊢
    have haux_eq :
        fieldsEventsAux (vecCap4Of v.base.recv.length) v.base.recv.length (fl :: fs) =
          mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl ++
            fieldsEventsAux (vecCap4Of (v.apply fl).base.recv.length)
              (v.apply fl).base.recv.length fs := by
      dsimp only [fieldsEventsAux]
      rw [nextCapRecv_eq_vecCap4Of v.base.recv.length fl, b518r3_apply_recv_len v fl]
      rfl
    rw [haux_eq] at hfit ⊢
    obtain ⟨hfit_fl, hfit_rest⟩ := (fitsEvents_append M lim _ _ st).mp hfit
    refine overDec_sepWPp_seq
      (hField st s0 s g v fl _ hany hok hfr1 hfb1 hpq hsuf hlen hfit_fl hregs) ?_
    rintro sm Pm - - ⟨hregsm, hentm⟩
    refine overDec_sepWPp_weaken_pre hentm ?_
    have hsuf' : fs.flatMap GenFieldQ.enc <:+ g.enc :=
      List.IsSuffix.trans (List.suffix_append _ _) hsuf
    rcases fs with _ | ⟨fl', fs'⟩
    · refine overDec_sepWPp_mono_post ?_
        (hNil
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          s0 sm g (v.apply fl) hlen hregsm)
      rintro sf P_f - - ⟨hregsf, hentf⟩
      refine ⟨hregsf, ?_⟩
      dsimp only [fieldsEventsAux, List.foldl]
      rw [List.append_nil]
      exact hentf
    · have hne : (fl' :: fs').flatMap GenFieldQ.enc ≠ [] := by
        rw [overDec_flatMap_cons]
        intro h
        exact overDec_enc_ne_nil fl' (List.append_eq_nil_iff.mp h).1
      refine overDec_sepWPp_seq
        (hCons
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          s0 sm g (v.apply fl) _ hne hsuf' hlen hregsm) ?_
      rintro sn Pn - - ⟨hregsn, hentn⟩
      refine overDec_sepWPp_weaken_pre hentn ?_
      refine overDec_sepWPp_mono_post ?_
        (ih
          (M.stepEvents (mergeFieldQEvents (vecCap4Of v.base.recv.length) v.base.recv.length fl) st)
          (v.apply fl) sn (List.cons_ne_nil _ _)
          (fun f hf => hmem f (List.mem_cons_of_mem _ hf)) hfr2 hfb2 hsuf' hfit_rest hregsn)
      rintro sf P_f - - ⟨hregsf, hentf⟩
      refine ⟨hregsf, ?_⟩
      rw [M.stepEvents_append]
      exact hentf

private theorem b518r3_fieldsEventsAux_empty_eq (fs : List GenFieldQ) :
    fieldsEventsAux (vecCap4Of SSGQ.empty.base.recv.length)
      SSGQ.empty.base.recv.length fs = fieldsEventsAux 0 0 fs :=
  rfl

private theorem b518r3_cast_loop [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {s0 sm : State} {g0 : OverDecG} {st0 : M.σ}
    {fs : List GenFieldQ} {v_out : SSGQ} {evs0 : List AllocEvent}
    (h1 : fs.flatMap GenFieldQ.enc = g0.enc)
    (h2 : fs.foldl SSGQ.apply SSGQ.empty = v_out)
    (h3 : fieldsEventsAux (vecCap4Of SSGQ.empty.base.recv.length)
      SSGQ.empty.base.recv.length fs = evs0)
    (hloop : SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) sm
      (b518x_overDecHeapCap A lim st0 sm g0 (fs.flatMap GenFieldQ.enc) SSGQ.empty)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g0 0x2620#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim
          (M.stepEvents
            (fieldsEventsAux (vecCap4Of SSGQ.empty.base.recv.length)
              SSGQ.empty.base.recv.length fs) st0)
          sf g0 [] (fs.foldl SSGQ.apply SSGQ.empty)))
      (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 9760#64) sm
      (b518x_overDecHeapCap A lim st0 sm g0 g0.enc SSGQ.empty)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g0 0x2620#64 sf ∧
        (P_f ⊢ b518x_overDecHeapCap A lim (M.stepEvents evs0 st0) sf g0 [] v_out))
      (fun _ _ => False) := by
  rw [h1, h2, h3] at hloop
  exact hloop

private theorem b518r3_fits_of_eq {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {xs ys : List AllocEvent} (h : xs = ys) (hf : FitsEvents M lim st ys) :
    FitsEvents M lim st xs :=
  h ▸ hf

private theorem b518r3_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sf : State)
    (q r19 r20 r26 prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) (sv : State) (v : SSGQ)
    (hne : enc ≠ []) :
    b518x_overDecHeapCap A lim st sf
      ⟨q, r19, r20, r26, prevCap, prevPtr, encCap, encPtr, enc, sv⟩ [] v ⊢
      overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
        overDecScratchPostBudget A q v ∗
        stackAt q overDecStackX ∗
        A.pool lim st sf ∗ anyHeap := by
  let g : OverDecG := ⟨q, r19, r20, r26, prevCap, prevPtr, encCap, encPtr, enc, sv⟩
  exact Entails.trans (b518x_overDecHeapCap_entails_budget A lim st sf g [] v)
    (overDec_exit_ext (A := A.atState lim st sf) g v hne)

private theorem b518r3_decode_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEntry : b518r3_EntryCro A lim ext)
    (hCons : b518r3_HeadConsCro A lim ext)
    (hNil : b518r3_HeadNilCro A lim ext)
    (hKey : b518r3_KeyCro A lim ext)
    (hVarint : b518r3_ArmCro A lim ext OverDecVarintField)
    (hBytes : b518r3_ArmCro A lim ext OverDecBytesField)
    (hSender : b518r3_ArmCro A lim ext OverDecSenderField)
    (hRecv : b518r3_ArmCro A lim ext OverDecRecvField)
    (st0 : M.σ) (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8))
    (Env : List AllocEvent → Prop)
    (fs : List GenFieldQ) (v_out : SSGQ) (evs_out : List AllocEvent)
    (hencfs : enc = fs.flatMap GenFieldQ.enc)
    (hfsne : fs ≠ [])
    (hlen : enc.length < 2 ^ 62)
    (hmem : ∀ fl ∈ fs, OverDecAnyField fl ∧ fl.Ok ∧ b518r3_NonEmptyPq fl)
    (hfr : OverDecFreshChain fs SSGQ.empty)
    (hfb : b518r3_FreshBytesChain fs SSGQ.empty)
    (hfold : fs.foldl SSGQ.apply SSGQ.empty = v_out)
    (haux0 : fieldsEventsAux (vecCap4Of SSGQ.empty.base.recv.length)
      SSGQ.empty.base.recv.length fs = evs_out)
    (hdes : Env evs_out)
    (hFit : FitsEnv M lim st0 Env)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcl : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64)
    (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 .x27 = prevPtr)
    (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        A.pool lim st0 s)
      (fun sf P_f =>
        (∃ evs, Env evs ∧
          (P_f ⊢ overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
              overDecScratchPostBudget A s.sp v_out ∗
              stackAt s.sp overDecStackX ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ anyHeap)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hne : enc ≠ [] := fun h0 => overDec_flatMap_ne_nil _ hfsne (hencfs.symm.trans h0)
  have hfit_evs : FitsEvents M lim st0 evs_out := hFit evs_out hdes
  have hEntry' := hEntry st0 s0 s
    ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26,
      prevCap, prevPtr, encCap, encPtr, enc, s⟩
    hne hlen hcro hcl hpc hrun rfl hal htr
    rfl rfl rfl hx21 hx24 hx25 hx27 hx29 rfl
  refine overDec_sepWPp_seq hEntry' ?_
  rintro sm Pm - - ⟨hregsm, hentm⟩
  refine overDec_sepWPp_weaken_pre hentm ?_
  have hField := b518r3_field_of_key_arm hKey
    (b518r3_arm_any hVarint hBytes hSender hRecv) (fun _ h => h)
  have hsuf : fs.flatMap GenFieldQ.enc <:+ enc :=
    ⟨[], by rw [List.nil_append, hencfs]⟩
  have hfit_fs :
      FitsEvents M lim st0
        (fieldsEventsAux (vecCap4Of SSGQ.empty.base.recv.length)
          SSGQ.empty.base.recv.length fs) :=
    b518r3_fits_of_eq haux0 hfit_evs
  have hloop0 := b518r3_loop hField hCons hNil s0
    ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26,
      prevCap, prevPtr, encCap, encPtr, enc, s⟩
    hlen fs st0 SSGQ.empty sm hfsne hmem hfr hfb hsuf hfit_fs hregsm
  have hloop := b518r3_cast_loop
    (g0 := ⟨s.sp, s.readReg64 .x19, s.readReg64 .x20, s.readReg64 .x26,
      prevCap, prevPtr, encCap, encPtr, enc, s⟩)
    hencfs.symm hfold haux0 hloop0
  refine overDec_sepWPp_mono_post ?_ hloop
  rintro sf P_f - - ⟨⟨hcrof, -, -, hsp, -, htrf, hclf, h19, h20, h26, h21, h24, h25, h27, -, h29,
      hvregsf⟩, hentf⟩
  have hexit := b518r3_exit_entails A lim (M.stepEvents evs_out st0) sf
    s.sp (s.readReg64 .x19) (s.readReg64 .x20) (s.readReg64 .x26)
    prevCap prevPtr encCap encPtr enc s v_out hne
  exact ⟨⟨evs_out, hdes, Entails.trans hentf hexit⟩,
    hsp, htrf, hcrof, hclf, h19, h20, h21, h24, h25, h26, h27, h29, hvregsf⟩

private theorem b518r3_len_lt62 {enc bs : List (BitVec 8)} (henc : enc = bs)
    (h : bs.length < 2 ^ 62) : enc.length < 2 ^ 62 :=
  henc ▸ h

private theorem b518r3_decode_of_steps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hEntry : b518r3_EntryCro A lim ext)
    (hCons : b518r3_HeadConsCro A lim ext)
    (hNil : b518r3_HeadNilCro A lim ext)
    (hKey : b518r3_KeyCro A lim ext)
    (hVarint : b518r3_ArmCro A lim ext OverDecVarintField)
    (hBytes : b518r3_ArmCro A lim ext OverDecBytesField)
    (hSender : b518r3_ArmCro A lim ext OverDecSenderField)
    (hRecv : b518r3_ArmCro A lim ext OverDecRecvField) :
    b518x_OverPrevDecodeExactCroPlacedAt A lim ext :=
  fun st0 s0 s prevCap prevPtr encCap encPtr enc sess hok hFit hcro hcl hpc hrun
    hal htr hx21 hx24 hx25 hx27 hx29 =>
  let hmem_base := overDec_mem_genFieldsQ sess hok.2.1 hok.2.2.2.1 hok.2.2.2.2
  let hpq_all := b518r3_nonEmptyPq_genFieldsQ sess
  b518r3_decode_core hEntry hCons hNil hKey hVarint hBytes hSender hRecv
    st0 s0 s prevCap prevPtr encCap encPtr enc
    (SessDeserializeCancelEnv ⟨some sess⟩)
    (genFieldsQ sess) (ssgqOf sess) (sessDeserEvents ⟨some sess⟩)
    (hok.1.trans (overDec_encSession_eq sess hok.2.1))
    (overDec_genFieldsQ_ne_nil sess hok.2.2.1)
    (b518r3_len_lt62 hok.1 (overDec_encSession_length_lt sess hok.2.1))
    (fun fl hfl => ⟨(hmem_base fl hfl).1, (hmem_base fl hfl).2, hpq_all fl hfl⟩)
    (overDec_freshChain_genFieldsQ sess hok.2.1)
    (b518r3_freshBytesChain_genFieldsQ sess)
    (overDec_fold_genFieldsQ sess hok.2.1)
    ((b518r3_fieldsEventsAux_empty_eq (genFieldsQ sess)).trans
      (b518x_fieldsEventsAux_genFieldsQ_eq_sessDeserEvents sess))
    ⟨hok.2.1, rfl⟩
    hFit
    hcro hcl hpc hrun hal htr hx21 hx24 hx25 hx27 hx29

/-- Block-`518` (`+0x1ee8..+0x2620`) exact-trace decode theorem under `AllocContractsPlaced`, `BytesMerge6Placed514OkExtW` (Block `514`), and capacity-pinned `b518x_ChainMerge5ExactCroPlacedOkExt'` (Block `516`). -/
theorem b518x_overPrevDecode_exact_cro_placed_of_alloc_bm6w_chain5'
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext) :
    b518x_OverPrevDecodeExactCroPlacedAt A lim ext :=
  b518r3_decode_of_steps
    (fun st s0 s g => b518x_entry_cro_placed ext st s0 s g)
    (fun st s0 s g v rest => b518x_headCons_cro_placed ext st s0 s g v rest)
    (fun st s0 s g v _hlen hregs => b518x_headNil_cro_placed ext st s0 s g v hregs)
    (fun st s0 s g v fl rest _hany _hok hsuf hlen hregs =>
      overDec_sepWPp_mono_post (fun _ _ _ _ ⟨h1, h2, _, h4⟩ => ⟨h1, h2, h4⟩)
        (b518x_key_cro_placed_of_alloc hAlloc st s0 s g v fl rest hsuf hlen hregs))
    (fun st s0 s g v fl rest hP _hok _hfr _hfb _hpq hsuf hlen _hfit hregs hx0 =>
      b518x_arm_varint_cro_placed_of_alloc hAlloc st s0 s g v fl rest hP hsuf hlen hregs hx0)
    (fun st s0 s g v fl rest hP hok hfr hfb hpq hsuf hlen hfit hregs hx0 =>
      b518x_arm_bytes_cro_placed_of_bm6w hBM6W st s0 s g v fl rest hP hok hfr hfb
        (fun b hb => by subst hb; exact hpq) hsuf hlen hfit hregs hx0)
    (b518r3_armSender hChain5)
    (b518r3_armRecv hAlloc hChain5)

/-- Hook-discharged Block-`518` (`+0x1ee8..+0x2620`) exact-trace decode theorem from single-step allocator, `memcpy`, `memmove`, and panic hooks plus `b518x_ChainMerge5ExactCroPlacedOkExt'`. -/
theorem b518x_overPrevDecode_exact_cro_placed_of_hooks_chain5'
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt' A lim ext) :
    b518x_OverPrevDecodeExactCroPlacedAt A lim ext :=
  b518x_overPrevDecode_exact_cro_placed_of_alloc_bm6w_chain5'
    (AllocContractsPlaced.of_hooks halloc hdealloc hrealloc
      (b518x_sessionShim_of_noAllocShim hshim) hmemmove)
    (bytes_merge_6_placed_ok_w_cro (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_raw)
    hChain5

theorem b518x_overPrevDecode_exact_cro_placed_of_alloc_bm6w_chain5
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext)
    (hBM6W : BytesMerge6Placed514OkExtW A lim ext)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt A lim ext) :
    b518x_OverPrevDecodeExactCroPlacedAt A lim ext :=
  b518x_overPrevDecode_exact_cro_placed_of_alloc_bm6w_chain5' hAlloc hBM6W
    (b518x_chainMerge5Exact_pinned_of_unpinned hChain5)

/-- Hook-discharged Block-`518` (`+0x1ee8..+0x2620`) exact-trace decode theorem parameterized by unpinned `b518x_ChainMerge5ExactCroPlacedOkExt`. -/
theorem b518x_overPrevDecode_exact_cro_placed_of_hooks_chain5
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat ext lsMemcpySym framelessMemcpyBudgetSpec)
    (hmemmove : HookSat ext "memmove" (sessionMemmoveBudgetSpec extHookStack))
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked)
    (hChain5 : b518x_ChainMerge5ExactCroPlacedOkExt A lim ext) :
    b518x_OverPrevDecodeExactCroPlacedAt A lim ext :=
  b518x_overPrevDecode_exact_cro_placed_of_alloc_bm6w_chain5
    (AllocContractsPlaced.of_hooks halloc hdealloc hrealloc
      (b518x_sessionShim_of_noAllocShim hshim) hmemmove)
    (bytes_merge_6_placed_ok_w_cro (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_raw)
    hChain5

/-- Lift `b518x_OverPrevDecodeExactCroPlacedAt` to the `b518x_VerNeSessionCancelRawEnv enc` envelope. -/
theorem b518x_overPrevDecode_rawEnv_cro_placed_of_exact
    [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hExact : b518x_OverPrevDecodeExactCroPlacedAt A lim ext)
    (st0 : M.σ) (s0 s : State) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) (sess : Session (List (BitVec 8)))
    (hok : OverPrevEncOKAt enc sess)
    (hfit : FitsEnv M lim st0 (b518x_VerNeSessionCancelRawEnv enc))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcl : (lsProg_518 ext).CodeLoaded s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64)
    (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = s.sp + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx27 : s.readReg64 .x27 = prevPtr)
    (hx29 : s.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗ overDecScratchPre s.sp ∗
        stackAt s.sp overDecStackX ∗
        A.pool lim st0 s)
      (fun sf P_f =>
        (∃ evs, b518x_VerNeSessionCancelRawEnv enc evs ∧
          (P_f ⊢ overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ∗
              overDecScratchPostBudget A s.sp (ssgqOf sess) ∗
              stackAt s.sp overDecStackX ∗
              A.pool lim (M.stepEvents evs st0) sf ∗ anyHeap)) ∧
        sf.sp = s.sp ∧ sf.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl sf.mem ∧
        (lsProg_518 ext).CodeLoaded sf.mem ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.sp + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  have hwp := hExact st0 s0 s prevCap prevPtr encCap encPtr enc sess hok
    (b518x_fitsExact_of_fitsRaw hok hfit) hcro hcl hpc hrun hal htr hx21 hx24 hx25 hx27 hx29
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpcsf, hrunsf, P_f, hmf, ⟨⟨evs, hdes, hent⟩, hrest⟩⟩ | hpan⟩ := hwp R hm hL
  · exact ⟨sf, hsteps, .inl ⟨hpcsf, hrunsf, P_f, hmf,
      ⟨⟨evs, b518x_verNeSessionCancelRawEnv_of_exact hok hdes, hent⟩, hrest⟩⟩⟩
  · exact ⟨sf, hsteps, .inr hpan⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ExactDecodePlacedBudget
