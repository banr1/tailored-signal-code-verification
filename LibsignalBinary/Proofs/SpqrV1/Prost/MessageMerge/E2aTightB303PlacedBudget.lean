/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedClPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.Ct1Received::merge` (Block `303`)

Proves `tlb_ChunkedCt1ReceivedMergePlacedTightOkOf` on Block `303` within
`SpqrTightEvs maxOps 384723 2560` (`ucOps + encOps ≤ maxOps`, default `43 = 8 + 35`:
`Unchunked.EkSentCt1Received` `42,108` B + `PolynomialEncoder` `342,615` B) on canonical
`tlb_ChunkedCt1ReceivedDom` inputs, falling back to `ChunkedCt1ReceivedMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB303PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_311 blkPl_311 libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_encodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_lt key_wt_some sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost protoEncodeVarint_eq_codec setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly (protoPolynomialEncoderPinnedAt vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1ReceivedMergeGhost ChunkedLoopRegs PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedBelow chunkedBelow_eq_poly chunkedBelow_eq_unchunked chunkedBelow_leaf
   chunkedBelow_leaf_entails chunkedCt1ReceivedMerge_fnOff chunkedCt1ReceivedPBCapAt
   chunkedCt1ReceivedPBCapAt_mono chunkedMergeStack chunkedSavedRegs
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   memRegion_ekSentCt1Received_none_split memRegion_polyEncoder_none_split
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optUnchunkedEkSentCt1ReceivedPBCapAt optUnchunkedEkSentCt1ReceivedPBCapAt_mono
   polyEncoderToProto protoPolynomialEncoderAt_eq_pb
   proto_mergeMessage_len_le proto_mergeMessage_suffix
   stackAt_chunkedMerge subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   vecU8At_eq_header_sep_buf vecU8Buf withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_303 blkPl_303)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1ReceivedDom tlb_ChunkedCt1ReceivedGuardedEnvOf
   tlb_ChunkedCt1ReceivedMergePlacedTightOk tlb_ChunkedCt1ReceivedMergePlacedTightOkOf
   tlb_GuardedEnv tlb_PolyEncoderDom tlb_PolyEncoderMergePlacedTightOkOf
   tlb_UcEkSentCt1ReceivedDom tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf
   tlb_ValidChunkedCt1ReceivedPB tlb_domHeap_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed
   tlb_polyEncoderMergeTightSpecOfEnv tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs
   tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv tlb_ucEkSentCt1ReceivedZeroCapAt
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudget
  (chunkedCt1Received_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1ReceivedBudgetAux
  (stackAt_chunkedMerge_epilogue)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergeEnv
   UnchunkedEkSentCt1ReceivedMergePostEnv chunkedCt1ReceivedMergePostEnv_imp_pre
   chunkedCt1ReceivedMergeSpec chunkedCt1ReceivedMergeSpecOfEnv decodeErrorPushMergeBudgetSpec
   unchunkedEkSentCt1ReceivedMergeSpec unchunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergeEnv PolyEncoderMergePostEnv polyEncoderMergeSpec polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem e2b303_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2b303_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2b303_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2b303_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2b303_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2b303_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2b303_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2b303_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2b303_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1ReceivedMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2b303_sp_setMem_pre e2b303_pc_setMem_pre e2b303_status_setMem_pre e2b303_pstate_setMem_pre
  e2b303_trace_setMem_pre e2b303_readReg64_setMem_pre e2b303_readReg32_setMem_pre
  e2b303_readReg_setMem_pre e2b303_calleeSavedVRegs_setMem_pre

private theorem e2b303_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ## 1. Cross-Block Transfer Helper to `(blkPC_303).rebase (blkPl_303).base` -/

private theorem e2b303_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-! ## 2. Zero-Capacity Initialization Fold Lemmas (`cap = 0#64` for Blocks `311` and `297`) -/

private theorem e2b303_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] := by
  refine Entails.trans ?_ (tlb_vecU8ZeroCapAt_of_ptr A a ptr [])
  rw [vecU8At_eq_header_sep_buf, vecHeader]; unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 := ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

private theorem e2b303_default_ekSentCt1Received_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40 ∗ ((a + 96#64) ↦₆₄ 0#64) ⊢
      tlb_ucEkSentCt1ReceivedZeroCapAt A a default := by
  unfold tlb_ucEkSentCt1ReceivedZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) [] ∗
    (((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 48#64 + 8#64) 40) ∗
    ((a + 96#64) ↦₆₄ 0#64)
  have h1 := e2b303_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b303_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_lin
  rw [h32, h40] at h2; rw [h56]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

private theorem e2b303_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecVecU8PinnedAt A ⟨0#64, ptr⟩ a [] := by
  unfold vecVecU8PinnedAt CryptoVerification.SpqrV1.Poly.vecHeaderBytes
    CryptoVerification.RustHeap.vecAt vecHeader vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0 := ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by dsimp only [List.length]; sep_ac_rfl)

private theorem e2b303_default_polyEncoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + 24#64) [] ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := e2b303_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h2 := e2b303_pointsTo_zero_entails_vecVecU8ZeroPin A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

/-! ## 3. Pure Codec Round-Trip Lemmas on `tlb_ChunkedCt1ReceivedDom` -/

private theorem e2b303_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> cases h
  rfl

private theorem e2b303_lenPrefixed_decodeVarint (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) = some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc, protoEncodeVarint_eq_codec]
  exact decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)

private theorem e2b303_lenPrefixed_length_gt (raw rest : List (BitVec 8)) :
    raw.length + rest.length < (tlb_lenPrefixed raw rest).length := by
  simpa only [List.length_append] using
    decodeVarint_length (e2b303_lenPrefixed_decodeVarint raw rest)

private theorem e2b303_mergeMessage_ch_ct1Received (pb : V1State.Chunked.Ct1Received)
    (rest : List (BitVec 8))
    (hraw : (V1State.Chunked.Ct1Received.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.Ct1Received.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.Ct1Received.encodeRaw pb) rest) 99).toOption =
      some (pb, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Chunked.Ct1Received.mergeField 2 V1State.Chunked.Ct1Received.encodeRaw
    default pb 99 rest
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_ch_ct1Received pb hraw) hraw (by decide)]
  rfl

private theorem e2b303_encodeOptMessage_tag1_some (u : V1State.Unchunked.EkSentCt1Received)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 (some u) ++ after =
      0x0a#8 :: tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited =
      [0x0a#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b303_decodeVarint_0x0a (r : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: r) = some (0x0a#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x0a#64 = [0x0a#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x0a#64 r

private theorem e2b303_mergeMessage_uc_ekSentCt1Received
    (u : V1State.Unchunked.EkSentCt1Received) (after : List (BitVec 8))
    (hraw : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length < 2 ^ 64) :
    (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) after) 98).toOption =
      some (u, after) := by
  change (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField .lengthDelimited
    default (tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) after) 98).toOption =
    some (u, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Unchunked.EkSentCt1Received.mergeField 1 V1State.Unchunked.EkSentCt1Received.encodeRaw
    default u 98 after
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_uc_ekSentCt1Received u hraw) hraw (by decide)]
  rfl

private theorem e2b303_encodeOptMessage_tag2_some (e : PolynomialEncoder)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 (some e) ++ after =
      0x12#8 :: tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited =
      [0x12#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b303_decodeVarint_0x12 (r : List (BitVec 8)) :
    decodeVarint (0x12#8 :: r) = some (0x12#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x12#64 = [0x12#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x12#64 r

private theorem e2b303_mergeMessage_polyEncoder (e : PolynomialEncoder)
    (after : List (BitVec 8))
    (hraw : (PolynomialEncoder.encodeRaw e).length < 2 ^ 64) :
    (mergeMessage PolynomialEncoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) after) 98).toOption =
      some (e, after) := by
  change (mergeMessage PolynomialEncoder.mergeField .lengthDelimited
    default (tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) after) 98).toOption =
    some (e, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw
    default e 98 after
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyEncoder e hraw) hraw (by decide)]
  rfl

/-! ## 4. Model-Generic `FitsEnv` Discharges & Guarded-Tight Envelope -/

/-- Parametric guarded-tight allocation envelope for Block `303` (`Chunked.Ct1Received::merge`):
enforces `SpqrTightEvs maxOps cumCap maxReq` on canonical `tlb_ChunkedCt1ReceivedDom` inputs and
falls back to `ChunkedCt1ReceivedMergeEnv` outside `tlb_ChunkedCt1ReceivedDom`. -/
def e2b303_ChunkedCt1ReceivedGuardedEnv (maxOps cumCap maxReq : Nat) :
    ChunkedCt1ReceivedMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedCt1ReceivedDom
    (SpqrTightEvs maxOps cumCap maxReq) ChunkedCt1ReceivedMergeEnv

private theorem e2b303_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs h
  rw [decodeVarint2Env_eq_nil_of_some hd h]
  trivial

private theorem e2b303_fitsEnv_uc_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ucOps ucCum ucReq maxOps cumCap maxReq : Nat}
    {x_uc : UnchunkedEkSentCt1ReceivedMergeGhost}
    (hOps : ucOps ≤ maxOps) (hCum : ucCum ≤ cumCap) (hReq : ucReq ≤ maxReq)
    (hDom_uc : tlb_UcEkSentCt1ReceivedDom x_uc)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim st
      (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
        (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv x_uc) := by
  intro evs h
  exact hFit evs (SpqrTightEvs.mono hOps hCum hReq (tlb_guardedEnv_tight_of_dom hDom_uc h))

private theorem e2b303_fitsEnv_poly_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {o₁ c₁ r₁ encOps encCum encReq maxOps cumCap maxReq : Nat}
    {evs₁ : List AllocEvent} {x_pe : PolyEncoderMergeGhost}
    (hOps : o₁ + encOps ≤ maxOps) (hCum : c₁ + encCum ≤ cumCap)
    (hReq : max r₁ encReq ≤ maxReq)
    (hevs₁ : SpqrTightEvs o₁ c₁ r₁ evs₁)
    (hDom_pe : tlb_PolyEncoderDom x_pe)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs₁ st)
      (tlb_GuardedEnv tlb_PolyEncoderDom
        (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv x_pe) := by
  intro evs₂ h₂
  have ht₂ := tlb_guardedEnv_tight_of_dom hDom_pe h₂
  have hall := hFit (evs₁ ++ evs₂) (SpqrTightEvs.mono hOps hCum hReq (hevs₁.append ht₂))
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp hall).2

/-! ## 5. Straight-Line `SepWPpLscro` Step Lemmas on `tlb_ChunkedCt1ReceivedDom` -/

private def e2b303_domLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State.Chunked.Ct1Received)
    (bs cur : List (BitVec 8)) : SepProp :=
  chunkedCt1ReceivedPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0 ∗
    A.pool lim (M.stepEvents evs st) s

private theorem e2b303_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {maxOps cumCap maxReq : Nat}
    (x : ChunkedCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedCt1ReceivedDom x)
    (hsome : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedCt1ReceivedMergeSpecOfEnv A lim
      (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
      (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)).post (x, st) s0 sf := by
  dsimp only [chunkedCt1ReceivedMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  refine sepConj_mono_right (sepConj_mono ?_
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.trans (Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _))
    (Entails.sepExists_right evs (Entails.refl _))

section Placed

set_option quotPrecheck false in
local notation "blkBase" => (blkPl_303).base

private theorem e2b303_dom_ok_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {cur : List (BitVec 8)} {limit : Nat}
    {evs : List AllocEvent}
    (hDom : tlb_ChunkedCt1ReceivedDom x)
    (heq_lim : cur.length = limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs)
    (hpc : s.pc = (blkPl_303).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit) (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (e2b303_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; rw [e2b303_domLoopPre, chunkedSavedRegs,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      arm64_norm, hsp])
    wp_steps
    apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗ (curPtr ↦ₛ cur) ⊢
        sliceCursorAfter x.slot x.ptr x.bs cur := by
      rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2b303_ok_exit_entails A lim st x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b303_dom_decode_key [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {iwt : WireType} {limit : Nat} {evs : List AllocEvent}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_303).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (e2b303_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost
          (chunkedCt1ReceivedMergeSpecOfEnv A lim
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (e2b303_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  let x_dv : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, curPtr, cur⟩
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b303_domLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_dv, M.stepEvents evs st))
      (ret_pc := blkBase + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp,
              e2b303_stackAt_decodeVarint2_raw_eq])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hcur_lt,
        e2b303_fitsEnv_decodeVarint2_of_some hd⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hshr := key_shr32_of_lt hk_lt
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := blkBase + 244#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv, hd,
        e2b303_stackAt_decodeVarint2_raw_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm01
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      rcases hsm01 with ⟨hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hd hevs_dv
      subst hevs_nil
      (conv => arg 4; simp only [AllocCostModel.stepEvents_nil, arm64_norm, wp_norm, hsp])
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b303_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2b303_domLoopPre]; sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
        (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        ⟨by simp only [arm64_norm, wp_norm, hx23_m],
         by simp only [arm64_norm, wp_norm, hx24_m],
         by simp only [arm64_norm, wp_norm, hx25_m],
         ⟨by simp only [arm64_norm, wp_norm, hx26_m],
          by simp only [arm64_norm, wp_norm, hx27_m],
          by simp only [arm64_norm, wp_norm, hx28_m],
          by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

private theorem e2b303_dom_tag1_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {ucOps ucCum ucReq maxOps cumCap maxReq : Nat}
    (hOps : ucOps ≤ maxOps) (hCum : ucCum ≤ cumCap) (hReq : ucReq ≤ maxReq)
    (hUcTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv)
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv))))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {u : V1State.Unchunked.EkSentCt1Received}
    {rest rest' : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hm_uc : m.uc = none)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hDom_uc : tlb_UcEkSentCt1ReceivedDom
      ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩)
    (huc_res : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (u, rest'))
    (hcont : ∀ (evs₁ : List AllocEvent) (s' : State),
      SpqrTightEvs ucOps ucCum ucReq evs₁ →
      s'.pc = (blkPl_303).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (e2b303_domLoopPre A lim st evs₁ s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some u } x.bs rest')
        (WppPost
          (chunkedCt1ReceivedMergeSpecOfEnv A lim
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.lengthDelimited).toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (e2b303_domLoopPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_vm (mid := blkBase + 344#64)
  by_vm_steps
    (conv => arg 4; rw [e2b303_domLoopPre, chunkedCt1ReceivedPBCapAt, hm_uc,
      optUnchunkedEkSentCt1ReceivedPBCapAt, memRegion_ekSentCt1Received_none_split x.msgPtr])
    (conv => arg 4; simp only [AllocCostModel.stepEvents_nil, noneCap,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w48
    apply SepWP.exists_elim; intro w40; apply SepWP.exists_elim; intro w32
    apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16
    apply SepWP.exists_elim; intro w8
    wp_steps
    apply SepWP.fold (e2b303_default_ekSentCt1Received_entails_zeroCap A.repAlloc x.msgPtr)
      (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    let x_uc : UnchunkedEkSentCt1ReceivedMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, restPtr, rest⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 311)
    wp_steps
    (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_unchunked s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_uc, st))
      (ret_pc := blkBase + 356#64) hUcTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv, x_uc, restPtr]
            simp only [tlb_domHeap_of_dom hDom_uc, sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        e2b303_fitsEnv_uc_tight hOps hCum hReq hDom_uc hFitTight⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le huc_res
    apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv,
        unchunkedEkSentCt1ReceivedMergeSpecOfEnv, x_uc, huc_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs₁
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_u
      wp_focus_pure; intro hsm0
      have hevs₁ : SpqrTightEvs ucOps ucCum ucReq evs₁ :=
        tlb_guardedEnv_tight_of_dom hDom_uc hevs_u
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp, ← chunkedBelow_eq_unchunked s0.sp])
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b303_domLoopPre A lim st evs₁ s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some u } x.bs rest')
        (by dsimp only [e2b303_domLoopPre, chunkedCt1ReceivedPBCapAt,
            optUnchunkedEkSentCt1ReceivedPBCapAt]; sep_entail)
      exact hcont evs₁ _ hevs₁
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        ⟨by simp only [arm64_norm, wp_norm, hx23_m],
         by simp only [arm64_norm, wp_norm, hx24_m],
         by simp only [arm64_norm, wp_norm, hx25_m],
         ⟨by simp only [arm64_norm, wp_norm, hx26_m],
          by simp only [arm64_norm, wp_norm, hx27_m],
          by simp only [arm64_norm, wp_norm, hx28_m],
          by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

private theorem e2b303_dom_tag2_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {o₁ c₁ r₁ encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hOps : o₁ + encOps ≤ maxOps) (hCum : c₁ + encCum ≤ cumCap)
    (hReq : max r₁ encReq ≤ maxReq)
    (hPolyTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Received} {e : PolynomialEncoder}
    {rest rest' : List (BitVec 8)} {limit : Nat} {evs₁ : List AllocEvent}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hevs₁ : SpqrTightEvs o₁ c₁ r₁ evs₁)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hm_pe : m.sendingEk = none)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt56 : rest.length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hDom_pe : tlb_PolyEncoderDom
      ⟨.lengthDelimited, x.msgPtr + 104#64, default, x.bufRef, x.slot,
        x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩)
    (hpe_res : (mergeMessage PolynomialEncoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (e, rest'))
    (hcont : ∀ (evs : List AllocEvent) (s' : State),
      SpqrTightEvs maxOps cumCap maxReq evs →
      s'.pc = (blkPl_303).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s'
        (e2b303_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingEk := some e } x.bs rest')
        (WppPost
          (chunkedCt1ReceivedMergeSpecOfEnv A lim
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = (blkPl_303).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.lengthDelimited).toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
      (e2b303_domLoopPre A lim st evs₁ s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply sepWPpLscro_of_vm (mid := blkBase + 288#64)
  by_vm_steps
    (conv => arg 4; rw [e2b303_domLoopPre, chunkedCt1ReceivedPBCapAt, hm_pe,
      optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split (x.msgPtr + 104#64)])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
    wp_steps
    apply SepWP.fold (e2b303_default_polyEncoder_entails_zeroCap A.repAlloc (x.msgPtr + 104#64))
      (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [← A.pool_of_vmPreserved hvm0]
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    let x_pe : PolyEncoderMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 104#64, default, x.bufRef, x.slot, restPtr, rest⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
    wp_steps
    (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_poly s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_pe, M.stepEvents evs₁ st))
      (ret_pc := blkBase + 300#64) hPolyTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [tlb_polyEncoderMergeTightSpecOfEnv, x_pe, restPtr]
            simp only [tlb_domHeap_of_dom hDom_pe, sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        by change 0 + rest.length < 2 ^ 56; omega,
        by change 0 + rest.length < 2 ^ 56; omega,
        e2b303_fitsEnv_poly_tight hOps hCum hReq hevs₁ hDom_pe hFitTight⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
    apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv,
        polyEncoderMergeSpecOfEnv, x_pe, hpe_res,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs₂
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_p
      wp_focus_pure; intro hsm0
      have hevs₂ : SpqrTightEvs encOps encCum encReq evs₂ :=
        tlb_guardedEnv_tight_of_dom hDom_pe hevs_p
      (conv => arg 4; simp only [← M.stepEvents_append evs₁ evs₂ st,
        arm64_norm, wp_norm, hsp, protoPolynomialEncoderAt_eq_pb, ← chunkedBelow_eq_poly s0.sp])
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      apply SepWP.fold
        (optUnchunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b303_domLoopPre A lim st (evs₁ ++ evs₂) s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingEk := some e } x.bs rest')
        (by dsimp only [e2b303_domLoopPre, chunkedCt1ReceivedPBCapAt, optPolynomialEncoderPBAt];
            sep_entail)
      exact hcont (evs₁ ++ evs₂) _ (SpqrTightEvs.mono hOps hCum hReq (hevs₁.append hevs₂))
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        ⟨by simp only [arm64_norm, wp_norm, hx23_m],
         by simp only [arm64_norm, wp_norm, hx24_m],
         by simp only [arm64_norm, wp_norm, hx25_m],
         ⟨by simp only [arm64_norm, wp_norm, hx26_m],
          by simp only [arm64_norm, wp_norm, hx27_m],
          by simp only [arm64_norm, wp_norm, hx28_m],
          by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

private theorem e2b303_dom_prologue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hpc : s0.pc = (blkPl_303).base) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0_wt : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (hx1_msg : s0.readReg64 .x1 = x.msgPtr)
    (hx2_buf : s0.readReg64 .x2 = x.bufRef)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hwt_ld : x.wt = .lengthDelimited)
    (hdv0 : decodeVarint x.bs = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s : State,
      s.pc = (blkPl_303).base + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot →
      s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      ChunkedLoopRegs s0 s →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s
        (e2b303_domLoopPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (WppPost
          (chunkedCt1ReceivedMergeSpecOfEnv A lim
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
            (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
          (x, st) R s0)
        (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s0
      (chunkedCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ (sliceCursorAt x.slot x.ptr x.bs ∗
          (A.pool lim st s0 ∗ stackAt s0.sp chunkedMergeStack))))
      (WppPost
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))
        (x, st) R s0)
      (WppPanicFalse R) := by
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64
      (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  let x_dv0 : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedMerge s0.sp, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr
    apply SepWP.exists_elim; intro v_fp
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_dv0, st))
      (ret_pc := blkBase + 56#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm,
              e2b303_stackAt_decodeVarint2_raw_eq])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf], hbs_lt,
        e2b303_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
    have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
    let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hsub := bv_len_sub_limit hge_len
    apply sepWPpLscro_of_vm (mid := blkBase + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
        e2b303_stackAt_decodeVarint2_raw_eq, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm01
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      rcases hsm01 with ⟨hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hevs_nil
      (conv => arg 4; simp only [AllocCostModel.stepEvents_nil, arm64_norm, wp_norm])
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
        (by sep_focus)
      wp_steps
      have hrest0_fold :
          (x.slot ↦₆₄ rest0Ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗
            (x.ptr ↦ₛ x.bs.take (x.bs.length - rest0.length)) ∗ (rest0Ptr ↦ₛ rest0) ⊢
          sliceCursorAfter x.slot x.ptr x.bs rest0 := by
        rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        dsimp only [rest0Ptr]
        exact Entails.of_eq (by sep_ac_rfl)
      apply SepWP.fold hrest0_fold (by dsimp only [rest0Ptr]; sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b303_domLoopPre A lim st [] s0 _ x.msgPtr x.bufRef x.slot x.ptr
          x.msg x.bs rest0)
        (by dsimp only [e2b303_domLoopPre, AllocCostModel.stepEvents_nil, chunkedSavedRegs];
            sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         ⟨by simp only [arm64_norm, wp_norm, hx26_m],
          by simp only [arm64_norm, wp_norm, hx27_m],
          by simp only [arm64_norm, wp_norm, hx28_m],
          by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

/-! ## 6. Canonical `Dom` Contract & Guarded-Tight Composition for Block `303` -/

private def e2b303_domOnlySpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps cumCap maxReq : Nat) :
    Spec (ChunkedCt1ReceivedMergeGhost × M.σ) :=
  let base := chunkedCt1ReceivedMergeSpecOfEnv A lim
    (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
    (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
  { base with pre := fun (x, st) s => ⌜tlb_ChunkedCt1ReceivedDom x⌝ ∗ base.pre (x, st) s }

private theorem e2b303_dom_only_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {ucOps ucCum ucReq encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hOps : ucOps + encOps ≤ maxOps)
    (hCum : ucCum + encCum ≤ cumCap)
    (hReq : max ucReq encReq ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv)
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv))))
    (hPolyTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)))) :
    subroutine_ok ((blkPC_303).rebase (blkPl_303).base H)
      (blkPl_303).base
      (withLsCodeRoLoaded lsmpl (e2b303_domOnlySpec A lim maxOps cumCap maxReq)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b303_domOnlySpec
  dsimp only [chunkedCt1ReceivedMergeSpecOfEnv]
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedCt1ReceivedMergeSpecOfEnv A lim
        (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
        (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)) (x, st) R s0)
    (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  intro hDom
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, hpts_0, _hpolys_0, hFit⟩
  have hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq) :=
    fun evs ht => hFit evs (Or.inl ⟨hDom, ht⟩)
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  rcases hDom with ⟨hwt_proto, hmsg_def, pb, rest_out, hvalid, hbs_eq⟩
  have hDom' : tlb_ChunkedCt1ReceivedDom x := ⟨hwt_proto, hmsg_def, pb, rest_out, hvalid, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := e2b303_wt_eq_lengthDelimited hwt_proto
  let raw := V1State.Chunked.Ct1Received.encodeRaw pb
  let bs_uc := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 pb.uc
  let bs_pe := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    PolynomialEncoder.encodeRaw 2#32 pb.sendingEk
  have hraw_def : raw = bs_uc ++ bs_pe := rfl
  have hlen_gt : raw.length + rest_out.length < x.bs.length := by
    rw [hbs_eq]; exact e2b303_lenPrefixed_length_gt raw rest_out
  have hraw_lt64 : raw.length < 2 ^ 64 := by omega
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, raw ++ rest_out) := by
    rw [hbs_eq]; exact e2b303_lenPrefixed_decodeVarint raw rest_out
  have hraw_bv : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  have hge_len : ¬ (raw ++ rest_out).length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hraw_bv, List.length_append]; omega
  have hlim_eq : (raw ++ rest_out).length - (BitVec.ofNat 64 raw.length).toNat = rest_out.length := by
    rw [hraw_bv, List.length_append]; omega
  have hsome_top : (mergeMessage V1State.Chunked.Ct1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, rest_out) := by
    rw [hwt_proto, hmsg_def, hbs_eq]
    exact e2b303_mergeMessage_ch_ct1Received pb rest_out hraw_lt64
  have hrest0_suf : IsDropSuffix x.bs (raw ++ rest_out) := decodeVarint_suffix hdv0
  have hrest0_le : (raw ++ rest_out).length ≤ x.bs.length :=
    Nat.le_of_lt (decodeVarint_length hdv0)
  let m₁ : V1State.Chunked.Ct1Received := { (default : V1State.Chunked.Ct1Received) with uc := pb.uc }
  let cur₁ : List (BitVec 8) := bs_pe ++ rest_out
  have h_stage2 : ∀ (o₁ c₁ r₁ : Nat) (evs₁ : List AllocEvent) (s₁ : State),
      o₁ + encOps ≤ maxOps →
      c₁ + encCum ≤ cumCap →
      max r₁ encReq ≤ maxReq →
      SpqrTightEvs o₁ c₁ r₁ evs₁ →
      cur₁.length ≤ x.bs.length →
      IsDropSuffix x.bs cur₁ →
      s₁.pc = blkBase + 192#64 →
      s₁.status = .Running → s₁.sp = s0.sp - 128#64 → s₁.trace = s0.trace →
      s₁.readReg64 (Reg.gpr 19#5) = x.bufRef → s₁.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s₁.readReg64 (Reg.gpr 21#5) = x.slot →
      s₁.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_out.length →
      ChunkedLoopRegs s0 s₁ →
      SepWPpLscro lsmpl ((blkPC_303).rebase (blkPl_303).base H) (s0.readReg64 Reg.lr) s₁
        (e2b303_domLoopPre A lim st evs₁ s0 s₁ x.msgPtr x.bufRef x.slot x.ptr m₁ x.bs cur₁)
        (WppPost (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)) (x, st) R s0)
        (WppPanicFalse R) := by
    intro o₁ c₁ r₁ evs₁ s₁ ho₁ hc₁ hr₁ hevs₁ hcur₁_le hcur₁_suf
      hpc₁ hrun₁ hsp₁ htr₁ hx19_1 hx20_1 hx21_1 hx22_1 hcs₁
    cases hpe : pb.sendingEk with
    | none =>
      have hcur₁_eq : cur₁ = rest_out := by
        simp only [cur₁, bs_pe, hpe, CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
          List.nil_append]
      have hm₁_eq : m₁ = pb := by dsimp only [m₁]; cases pb; cases hpe; rfl
      rw [hcur₁_eq] at hcur₁_le hcur₁_suf ⊢
      rw [hm₁_eq]
      have ho₁' : o₁ ≤ maxOps := by omega
      have hc₁' : c₁ ≤ cumCap := by omega
      have hr₁' : r₁ ≤ maxReq := Nat.le_trans (Nat.le_max_left r₁ encReq) hr₁
      exact e2b303_dom_ok_exit hDom' rfl hsp_align hcur₁_le hcur₁_suf hsome_top
        (SpqrTightEvs.mono ho₁' hc₁' hr₁' hevs₁)
        hpc₁ hrun₁ hsp₁ htr₁ hx21_1 hx22_1 hcs₁
    | some e =>
      let r2 := tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) rest_out
      have hcur₁_eq : cur₁ = 0x12#8 :: r2 := by
        dsimp only [cur₁, bs_pe, r2]
        rw [hpe]
        exact e2b303_encodeOptMessage_tag2_some e rest_out
      have hr2_gt : (PolynomialEncoder.encodeRaw e).length + rest_out.length < r2.length :=
        e2b303_lenPrefixed_length_gt (PolynomialEncoder.encodeRaw e) rest_out
      have hgt_lim2 : ¬ cur₁.length ≤ rest_out.length := by
        rw [hcur₁_eq, List.length_cons]; omega
      have hcur₁_lt : cur₁.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur₁_le hbs_lt
      have hd2 : decodeVarint cur₁ = some (0x12#64, r2) := by
        rw [hcur₁_eq]; exact e2b303_decodeVarint_0x12 r2
      refine e2b303_dom_decode_key hVarintCall hgt_lim2 hsp_align hcur₁_le hcur₁_lt hcur₁_suf
        hd2 (by decide) (by decide : WireType.ofNat? ((0x12#64).toNat % 8) = some .lengthDelimited)
        (by decide) ?_ hpc₁ hrun₁ hsp₁ htr₁ hx19_1 hx20_1 hx21_1 hx22_1 hcs₁
      intro s₂ hpc₂ hrun₂ hsp₂ htr₂ hx0_2 hx1_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs₂
      have hr2_le_cur₁ : r2.length ≤ cur₁.length := Nat.le_of_lt (decodeVarint_length hd2)
      have hr2_le : r2.length ≤ x.bs.length := Nat.le_trans hr2_le_cur₁ hcur₁_le
      have hr2_lt56 : r2.length < 2 ^ 56 := Nat.lt_of_le_of_lt hr2_le hbs_lt56
      have hr2_suf : IsDropSuffix x.bs r2 :=
        suffix_trans hcur₁_le hcur₁_suf hr2_le_cur₁ (decodeVarint_suffix hd2)
      have he_lt64 : (PolynomialEncoder.encodeRaw e).length < 2 ^ 64 := by omega
      have hDom_pe : tlb_PolyEncoderDom
          ⟨.lengthDelimited, x.msgPtr + 104#64, default, x.bufRef, x.slot,
            x.ptr + BitVec.ofNat 64 (x.bs.length - r2.length), r2⟩ :=
        ⟨rfl, rfl, e, rest_out, hvalid.2 e hpe, rfl⟩
      have hpe_res : (mergeMessage PolynomialEncoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default r2 98).toOption = some (e, rest_out) :=
        e2b303_mergeMessage_polyEncoder e rest_out he_lt64
      have hx1_2' : s₂.readReg64 (Reg.gpr 1#5) = 2#64 := hx1_2
      refine e2b303_dom_tag2_step ho₁ hc₁ hr₁ hPolyTightCall hFitTight hevs₁ hsp_align rfl
        hr2_le hr2_lt56 hr2_suf hDom_pe hpe_res ?_
        hpc₂ hrun₂ hsp₂ htr₂ hx0_2 hx1_2' hx19_2 hx20_2 hx21_2 hx22_2 hcs₂
      intro evs s₃ hevs hpc₃ hrun₃ hsp₃ htr₃ hx21_3 hx22_3 hcs₃
      have hpf := proto_mergeMessage_suffix hpe_res
      have hrest_out_le : rest_out.length ≤ x.bs.length := Nat.le_trans hpf.1 hr2_le
      have hrest_out_suf : IsDropSuffix x.bs rest_out :=
        suffix_trans hr2_le hr2_suf hpf.1 hpf.2
      have hm₂_eq : { m₁ with sendingEk := some e } = pb := by
        dsimp only [m₁]; cases pb; cases hpe; rfl
      rw [hm₂_eq]
      exact e2b303_dom_ok_exit hDom' rfl hsp_align hrest_out_le hrest_out_suf hsome_top hevs
        hpc₃ hrun₃ hsp₃ htr₃ hx21_3 hx22_3 hcs₃
  refine e2b303_dom_prologue hVarintCall hpc hrun hsp_align hx0_wt hx1_msg hx2_buf
    hbs_lt hwt_ld hdv0 hge_len ?_
  intro s₀' hpc₀' hrun₀' hsp₀' htr₀' hx19_0 hx20_0 hx21_0 hx22_0 hcs₀'
  rw [hlim_eq] at hx22_0
  rw [hmsg_def]
  have hrest0_eq : raw ++ rest_out = bs_uc ++ cur₁ := by
    simp only [hraw_def, cur₁, List.append_assoc]
  rw [hrest0_eq] at hrest0_le hrest0_suf ⊢
  cases huc : pb.uc with
  | none =>
    have hbs_uc_nil : bs_uc = [] := by
      simp only [bs_uc, huc, CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage]
    rw [hbs_uc_nil, List.nil_append] at hrest0_le hrest0_suf ⊢
    have hm_none : (default : V1State.Chunked.Ct1Received) = m₁ := by
      dsimp only [m₁]; rw [huc]; rfl
    rw [hm_none]
    exact h_stage2 0 0 0 [] s₀' (by omega) (by omega)
      (Nat.le_trans (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_max_right ucReq encReq⟩) hReq)
      (SpqrTightEvs.nil 0 0 0) hrest0_le hrest0_suf
      hpc₀' hrun₀' hsp₀' htr₀' hx19_0 hx20_0 hx21_0 hx22_0 hcs₀'
  | some u =>
    let r1 := tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) cur₁
    have hcur0_eq : bs_uc ++ cur₁ = 0x0a#8 :: r1 := by
      dsimp only [bs_uc, r1]
      rw [huc]
      exact e2b303_encodeOptMessage_tag1_some u cur₁
    rw [hcur0_eq] at hrest0_le hrest0_suf ⊢
    have hr1_gt : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length + cur₁.length <
        r1.length :=
      e2b303_lenPrefixed_length_gt (V1State.Unchunked.EkSentCt1Received.encodeRaw u) cur₁
    have hcur₁_ge_out : rest_out.length ≤ cur₁.length := by
      simp only [cur₁, List.length_append]; omega
    have hgt_lim1 : ¬ (0x0a#8 :: r1).length ≤ rest_out.length := by
      rw [List.length_cons]; omega
    have hcur0_lt : (0x0a#8 :: r1).length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hd1 : decodeVarint (0x0a#8 :: r1) = some (0x0a#64, r1) := e2b303_decodeVarint_0x0a r1
    refine e2b303_dom_decode_key hVarintCall hgt_lim1 hsp_align hrest0_le hcur0_lt hrest0_suf
      hd1 (by decide) (by decide : WireType.ofNat? ((0x0a#64).toNat % 8) = some .lengthDelimited)
      (by decide) ?_ hpc₀' hrun₀' hsp₀' htr₀' hx19_0 hx20_0 hx21_0 hx22_0 hcs₀'
    intro s_k hpc_k hrun_k hsp_k htr_k hx0_k hx1_k hx19_k hx20_k hx21_k hx22_k hcs_k
    have hr1_le_cur0 : r1.length ≤ (0x0a#8 :: r1).length := Nat.le_of_lt (decodeVarint_length hd1)
    have hr1_le : r1.length ≤ x.bs.length := Nat.le_trans hr1_le_cur0 hrest0_le
    have hr1_lt : r1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hr1_le hbs_lt
    have hr1_suf : IsDropSuffix x.bs r1 :=
      suffix_trans hrest0_le hrest0_suf hr1_le_cur0 (decodeVarint_suffix hd1)
    have hu_lt64 : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length < 2 ^ 64 := by omega
    have hDom_uc : tlb_UcEkSentCt1ReceivedDom
        ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - r1.length), r1⟩ :=
      ⟨rfl, rfl, u, cur₁, hvalid.1 u huc, rfl⟩
    have huc_res : (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto .lengthDelimited) default r1 98).toOption = some (u, cur₁) :=
      e2b303_mergeMessage_uc_ekSentCt1Received u cur₁ hu_lt64
    have hx1_k' : s_k.readReg64 (Reg.gpr 1#5) = 1#64 := hx1_k
    refine e2b303_dom_tag1_step (by omega) (by omega)
      (Nat.le_trans (Nat.le_max_left ucReq encReq) hReq)
      hUcTightCall hFitTight hsp_align rfl hr1_le hr1_lt hr1_suf hDom_uc huc_res ?_
      hpc_k hrun_k hsp_k htr_k hx0_k hx1_k' hx19_k hx20_k hx21_k hx22_k hcs_k
    intro evs₁ s₁ hevs₁ hpc₁ hrun₁ hsp₁ htr₁ hx19_1 hx20_1 hx21_1 hx22_1 hcs₁
    have huf := proto_mergeMessage_suffix huc_res
    have hcur₁_le : cur₁.length ≤ x.bs.length := Nat.le_trans huf.1 hr1_le
    have hcur₁_suf : IsDropSuffix x.bs cur₁ := suffix_trans hr1_le hr1_suf huf.1 huf.2
    have hm₁_some : { (default : V1State.Chunked.Ct1Received) with uc := some u } = m₁ := by
      dsimp only [m₁]; rw [huc]
    rw [hm₁_some]
    exact h_stage2 ucOps ucCum ucReq evs₁ s₁ hOps hCum hReq hevs₁ hcur₁_le hcur₁_suf
      hpc₁ hrun₁ hsp₁ htr₁ hx19_1 hx20_1 hx21_1 hx22_1 hcs₁

end Placed

/-- Fully parametric Block `303` (`V1State.Chunked.Ct1Received::merge`) guarded-tight contract on
`(blkPC_303).rebase (blkPl_303).base H`: composes any tight
`Unchunked.EkSentCt1Received::merge` (`Block 311`, over `tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv`)
envelope `(ucOps, ucCum, ucReq)` and tight `PolynomialEncoder::merge` (`Block 297`, over
`tlb_polyEncoderMergeTightSpecOfEnv`) envelope `(encOps, encCum, encReq)` into
`(maxOps, cumCap, maxReq)` whenever `ucOps + encOps ≤ maxOps`, `ucCum + encCum ≤ cumCap`, and
`max ucReq encReq ≤ maxReq`. -/
theorem e2b303_chunkedCt1Received_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {ucOps ucCum ucReq encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hOps : ucOps + encOps ≤ maxOps)
    (hCum : ucCum + encCum ≤ cumCap)
    (hReq : max ucReq encReq ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv)
          (tlb_GuardedEnv tlb_UcEkSentCt1ReceivedDom
            (SpqrTightEvs ucOps ucCum ucReq) UnchunkedEkSentCt1ReceivedMergeEnv))))
    (hPolyTightCall : subroutine_ok ((blkPC_303).rebase (blkPl_303).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom
            (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)))) :
    subroutine_ok ((blkPC_303).rebase (blkPl_303).base H)
      (blkPl_303).base
      (withLsCodeRoLoaded lsmpl
        (chunkedCt1ReceivedMergeSpecOfEnv A lim
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq)
          (e2b303_ChunkedCt1ReceivedGuardedEnv maxOps cumCap maxReq))) := by
  have hDomOk := e2b303_dom_only_subroutine_ok hOps hCum hReq
    hVarintCall hUcTightCall hPolyTightCall
  have hKleene := chunkedCt1Received_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : tlb_ChunkedCt1ReceivedDom x.1
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2b303_domOnlySpec A lim maxOps cumCap maxReq)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2b303_domOnlySpec]
      exact sepConj_mono_left (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _)))
    exact hDomOk.mono_outcome x R s0 hpc hrun hpre_dom hsp fun _ out => out
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (chunkedCt1ReceivedMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun hp =>
        Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩ (Entails.refl _)
      exact fun evs he => hp.2.2.2.2.2 evs (Or.inr ⟨hDom, he⟩)
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, chunkedCt1ReceivedMergeSpec, chunkedCt1ReceivedMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, chunkedCt1ReceivedMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, chunkedCt1ReceivedMergeSpec,
        chunkedCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt1ReceivedMergeSpec,
        chunkedCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt1ReceivedMergeSpec,
        chunkedCt1ReceivedMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-- Guarded-tight contract `tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim maxOps ext` on
`libsignalSessionLib.blockProgram lsmpl 303 (Rust.withPanics ext)` (`ucOps + encOps ≤ maxOps`). -/
theorem e2b303_chunkedCt1Received_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {ucOps encOps maxOps : Nat}
    (hOps : ucOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim ucOps ext)
    (hPolyTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedCt1ReceivedMergePlacedTightOkOf A lim maxOps ext := by
  have hok := e2b303_chunkedCt1Received_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext)
    (ucOps := ucOps) (ucCum := 42108) (ucReq := 2560)
    (encOps := encOps) (encCum := 342615) (encReq := 2560)
    (maxOps := maxOps) (cumCap := 384723) (maxReq := 2560)
    hOps (by decide) (by decide)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_311).rebase (blkPl_311).base (fun _ => none))) hUcUntight)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyUntight)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (blkPC_311).rebase (blkPl_311).base (fun _ => none))) hUcTight)
    (e2b303_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyTight)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_303).rebase (blkPl_303).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 303)] at hok
  exact hok

/-- Default `maxOps = 43` (`8 + 35`) specialization proving
`tlb_ChunkedCt1ReceivedMergePlacedTightOk`. -/
theorem e2b303_chunkedCt1Received_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyUntight : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim 8 ext)
    (hPolyTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedCt1ReceivedMergePlacedTightOk A lim ext :=
  e2b303_chunkedCt1Received_merge_placed_tight_ok_of (Nat.le_refl 43)
    hFrom hPush hVarint hSkip hUcUntight hPolyUntight hUcTight hPolyTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB303PlacedBudget
