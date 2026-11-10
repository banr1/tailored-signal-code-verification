/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.Ct1Acknowledged::merge` (Block `307`)

Proves `tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf` on Block `307` within
`SpqrTightEvs maxOps 388717 2560` (`ucOps + decOps ≤ maxOps`, default `45 = 10 + 35`:
`Unchunked.Ct1Sent` `46,102` B + `PolynomialDecoder` `342,615` B) on canonical
`tlb_ChunkedCt1AcknowledgedDom` inputs, falling back to `ChunkedCt1AcknowledgedMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB307PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261 instIsLsBlockProg_263
   instIsLsBlockProg_291 instIsLsBlockProg_312 libsignalMutatedBlocks libsignalSessionExterns
   libsignalSessionLib ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq lsmpl
   withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix iwt_w0_setWidth8
   key_shr32_of_lt key_wt_some
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeKey encodeMessage encodeOptMessage encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderPinnedAt protoPolynomialDecoderPtsNeededOff
   protoPolynomialDecoderPolysOff protoPolynomialDecoderIsCompleteOff
   protoPolynomialDecoderPadOff protoPolynomialDecoderPadSize
   vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.ProtoRepr
  (optPolynomialDecoderPBAt vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1AcknowledgedMergeGhost ChunkedLoopRegs PolyDecoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedBelow chunkedBelow_eq_poly
   chunkedBelow_eq_unchunked chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedCt1AcknowledgedMerge_fnOff chunkedCt1AcknowledgedPBCapAt
   chunkedCt1AcknowledgedPBCapAt_mono chunkedMergeStack chunkedSavedRegs
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   instIsLsBlockProg_296 memRegion_ct1Sent_none_split memRegion_polyDecoder_none_split
   optPolyDecoderPtsLen optUnchunkedCt1SentPBCapAt optUnchunkedCt1SentPBCapAt_mono
   pointsTo64_zero_eq_pointsTo32_pair polyDecoderToProto
   protoPolynomialDecoderAt_eq_pb proto_mergeMessage_len_le proto_mergeMessage_suffix
   setWidth8_ofNat64_wt stackAt_chunkedMerge
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp vecU8At_eq_header_sep_buf vecU8Buf
   withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkPC_307 blkPl_307 instIsLsBlockProg_307)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_ct1Acknowledged loopsTo_polyDecoder loopsTo_uc_ct1Sent
   mergeMessage_encode proto_decodeVarint_encodeVarint)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1AcknowledgedDom
   tlb_ChunkedCt1AcknowledgedGuardedEnvOf
   tlb_ChunkedCt1AcknowledgedMergePlacedTightOk
   tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf
   tlb_GuardedEnv
   tlb_PolyDecoderDom
   tlb_PolyDecoderGuardedEnvOf
   tlb_PolyDecoderMergePlacedTightOk
   tlb_PolyDecoderMergePlacedTightOkOf
   tlb_UcCt1SentDom
   tlb_UcCt1SentGuardedEnvOf
   tlb_UcCt1SentMergePlacedTightOk
   tlb_UcCt1SentMergePlacedTightOkOf
   tlb_ValidPolyDecoderPB
   tlb_ValidUcCt1SentPB
   tlb_domHeap_of_dom
   tlb_fitsEnv_fallback_of_not_dom
   tlb_lenPrefixed
   tlb_polyDecoderMergeTightSpecOfEnv
   tlb_polyDecoderZeroCapAt
   tlb_polyDecoderZeroCapAt_of_ptr
   tlb_ucCt1SentMergeTightSpecOfEnv
   tlb_ucCt1SentZeroCapAt
   tlb_vecU8ZeroCapAt
   tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedBudgetAux
  (stackAt_chunkedMerge_epilogue stackAt_decodeVarint2_raw_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1AcknowledgedClPlacedBudget
  (chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1AcknowledgedMergePostEnv UnchunkedCt1SentMergePostEnv
   chunkedCt1AcknowledgedMergePostEnv_imp_pre
   chunkedCt1AcknowledgedMergeSpec chunkedCt1AcknowledgedMergeSpecOfEnv
   decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec unchunkedCt1SentMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergePostEnv polyDecoderMergeSpec polyDecoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
  chunkedCt1AcknowledgedMerge_fnOff setWidth8_ofNat64_wt

@[local simp, local arm64_norm]
private theorem e2b307_iwt_w0_setWidth8_1 (iwt : WireType) :
    (BitVec.zeroExtend 64 ((BitVec.ofNat 64 iwt.toNat).setWidth 32)).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat :=
  (iwt_w0_setWidth8 iwt).1

@[local simp, local arm64_norm]
private theorem e2b307_iwt_w0_trunc32_zext64_setWidth8 (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

/-! ## 1. Own-Block / Caller-Block Transfer Helpers (`e2b307_`) -/

private class e2b307_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 307 :=
  ⟨by decide, by decide, (instIsLsBlockProg_307 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b307_IsLsValidBlock 312 :=
  ⟨by decide, by decide, (instIsLsBlockProg_312 (fun _ => none)).externs_eq⟩

private theorem e2b307_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2b307_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hfr0.1 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc,
      (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem e2b307_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2b307_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2b307_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2b307_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Pure Codec, Zero-Cap Initialization, and Tight `FitsEnv` Helpers (`e2b307_`) -/

private theorem e2b307_wt_eq_ld {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> cases h
  rfl

private theorem e2b307_decodeVarint_encodeVarint (v : BitVec 64) (rest : List (BitVec 8)) :
    decodeVarint (encodeVarint v ++ rest) = some (v, rest) := by
  rw [← proto_decodeVarint_toOption, proto_decodeVarint_encodeVarint]
  rfl

private theorem e2b307_encodeOpt_uc_some (u : V1State.Unchunked.Ct1Sent)
    (after : List (BitVec 8)) :
    encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 (some u) ++ after =
      encodeVarint 10#64 ++ tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after := by
  have hk : encodeKey 1#32 .lengthDelimited = [10#8] := by decide
  have hv : encodeVarint 10#64 = [10#8] := by decide
  simp [encodeOptMessage, encodeMessage, tlb_lenPrefixed, hk, hv, List.append_assoc]

private theorem e2b307_encodeOpt_dec_some (d : PolynomialDecoder)
    (after : List (BitVec 8)) :
    encodeOptMessage PolynomialDecoder.encodeRaw 2#32 (some d) ++ after =
      encodeVarint 18#64 ++ tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after := by
  have hk : encodeKey 2#32 .lengthDelimited = [18#8] := by decide
  have hv : encodeVarint 18#64 = [18#8] := by decide
  simp [encodeOptMessage, encodeMessage, tlb_lenPrefixed, hk, hv, List.append_assoc]

private theorem e2b307_mergeMessage_top_dom {wt : WireType}
    {pb : V1State.Chunked.Ct1Acknowledged} {tail : List (BitVec 8)}
    (hwt : codecWireTypeToProto wt = .lengthDelimited)
    (hraw_lt : (V1State.Chunked.Ct1Acknowledged.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField
      (codecWireTypeToProto wt) default
      (tlb_lenPrefixed (V1State.Chunked.Ct1Acknowledged.encodeRaw pb) tail) 99).toOption =
      some (pb, tail) := by
  rw [hwt]
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode V1State.Chunked.Ct1Acknowledged.mergeField 2
      V1State.Chunked.Ct1Acknowledged.encodeRaw default pb 99 tail
      (loopsTo_ch_ct1Acknowledged pb hraw_lt) hraw_lt (by decide)]
  rfl

private theorem e2b307_mergeMessage_uc {u : V1State.Unchunked.Ct1Sent}
    {after : List (BitVec 8)}
    (hu_lt : (V1State.Unchunked.Ct1Sent.encodeRaw u).length < 2 ^ 64) :
    (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after) 98).toOption =
      some (u, after) := by
  change (mergeMessage V1State.Unchunked.Ct1Sent.mergeField .lengthDelimited default
    (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after) 98).toOption = some (u, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode V1State.Unchunked.Ct1Sent.mergeField 1
      V1State.Unchunked.Ct1Sent.encodeRaw default u 98 after
      (loopsTo_uc_ct1Sent u hu_lt) hu_lt (by decide)]
  rfl

private theorem e2b307_mergeMessage_polyDec {d : PolynomialDecoder}
    {after : List (BitVec 8)}
    (hd_lt : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64) :
    (mergeMessage PolynomialDecoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after) 98).toOption =
      some (d, after) := by
  change (mergeMessage PolynomialDecoder.mergeField .lengthDelimited default
    (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after) 98).toOption = some (d, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode PolynomialDecoder.mergeField 0
      PolynomialDecoder.encodeRaw default d 98 after
      (loopsTo_polyDecoder d hd_lt) hd_lt (by decide)]
  rfl

private theorem e2b307_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] := by
  refine Entails.trans ?_ (tlb_vecU8ZeroCapAt_of_ptr A a ptr [])
  rw [vecU8At_eq_header_sep_buf, vecHeader]; unfold vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

private theorem e2b307_default_ct1Sent_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 80#64) 40 ∗
      ((a + 120#64) ↦₆₄ 0#64) ⊢
      tlb_ucCt1SentZeroCapAt A a default := by
  unfold tlb_ucCt1SentZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗
    tlb_vecU8ZeroCapAt A (a + 24#64) [] ∗
    tlb_vecU8ZeroCapAt A (a + 48#64) [] ∗
    ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64 ∗ memRegion (a + 72#64 + 8#64) 40) ∗
    ((a + 120#64) ↦₆₄ 0#64)
  have h1 := e2b307_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b307_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h3 := e2b307_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 48#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_lin
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_lin
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_lin
  rw [h32, h40] at h2; rw [h56, h64] at h3; rw [h80]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

private theorem e2b307_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecVecU8PinnedAt A ⟨0#64, ptr⟩ a [] := by
  unfold vecVecU8PinnedAt vecAt vecHeader vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  have hp : ptr ≠ 0#64 ∧ ([] : List (List (BitVec 8))).length ≤ (0#64).toNat ∧
      CryptoVerification.SpqrV1.Poly.vecHeaderBytes * (0#64).toNat < 2 ^ 63 :=
    ⟨hptr, by decide, by decide⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by
    dsimp only [List.length, CryptoVerification.SpqrV1.Poly.vecHeaderBytes]
    sep_ac_rfl)

private theorem e2b307_default_polyDecoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7 ⊢
      tlb_polyDecoderZeroCapAt A p (polyDecoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyDecoderZeroCapAt_of_ptr A 8#64 p (polyDecoderToProto default))
  unfold protoPolynomialDecoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    ((p + protoPolynomialDecoderPtsNeededOff) ↦₃₂ 0#32) ∗
    ((p + protoPolynomialDecoderPolysOff) ↦₃₂ 0#32) ∗
    ((p + protoPolynomialDecoderIsCompleteOff) ↦₈ 0#8) ∗
    memRegion (p + protoPolynomialDecoderPadOff) protoPolynomialDecoderPadSize
  dsimp only [protoPolynomialDecoderPtsNeededOff, protoPolynomialDecoderPolysOff,
    protoPolynomialDecoderIsCompleteOff, protoPolynomialDecoderPadOff,
    protoPolynomialDecoderPadSize]
  have h1 := e2b307_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
  rw [pointsTo64_zero_eq_pointsTo32_pair (p + 24#64), h28]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

private theorem e2b307_tight_of_guarded_dom {α : Type} {Dom : α → Prop}
    {Tight : List AllocEvent → Prop} {Fallback : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent}
    (hDom : Dom x) (h : tlb_GuardedEnv Dom Tight Fallback x evs) :
    Tight evs := by
  rcases h with ⟨_, ht⟩ | ⟨hnot, _⟩
  · exact ht
  · exact (hnot hDom).elim

private theorem e2b307_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {maxOps : Nat} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    {evs₀ : List AllocEvent}
    (hd : decodeVarint bs = some p)
    (hevs₀ : SpqrTightEvs maxOps 388717 2560 evs₀)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (DecodeVarint2Env bs) := by
  intro evs hevs
  have hnil : evs = [] := decodeVarint2Env_eq_nil_of_some hd hevs
  subst hnil
  exact ((fitsEvents_append M lim evs₀ [] st).mp
    (by simpa only [List.append_nil] using hFit evs₀ hevs₀)).2

private theorem e2b307_fitsEnv_uc_of_dom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ucOps maxOps : Nat} {x_uc : UnchunkedCt1SentMergeGhost}
    (hOps : ucOps ≤ maxOps)
    (hDomUc : tlb_UcCt1SentDom x_uc)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560)) :
    FitsEnv M lim st (tlb_UcCt1SentGuardedEnvOf ucOps x_uc) := by
  intro evs hevs
  have ht : SpqrTightEvs ucOps 46102 2560 evs :=
    e2b307_tight_of_guarded_dom hDomUc hevs
  exact hFit evs (ht.mono hOps (by decide) (Nat.le_refl 2560))

private theorem e2b307_fitsEnv_polyDec_of_dom {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ucOps decOps maxOps : Nat} {x_poly : PolyDecoderMergeGhost} {evs_u : List AllocEvent}
    (hOps : ucOps + decOps ≤ maxOps)
    (hDomDec : tlb_PolyDecoderDom x_poly)
    (hevs_u : SpqrTightEvs ucOps 46102 2560 evs_u)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560)) :
    FitsEnv M lim (M.stepEvents evs_u st) (tlb_PolyDecoderGuardedEnvOf decOps x_poly) := by
  intro evs_d hevs_d
  have ht_d : SpqrTightEvs decOps 342615 2560 evs_d :=
    e2b307_tight_of_guarded_dom hDomDec hevs_d
  have ht_all : SpqrTightEvs maxOps 388717 2560 (evs_u ++ evs_d) :=
    (hevs_u.append ht_d).mono hOps (by decide) (by decide)
  exact ((fitsEvents_append M lim evs_u evs_d st).mp (hFit (evs_u ++ evs_d) ht_all)).2

/-! ## 3. Canonical `tlb_ChunkedCt1AcknowledgedDom` Path (`e2b307_`) -/

private def e2b307_domSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedCt1AcknowledgedMergeGhost × M.σ) :=
  { chunkedCt1AcknowledgedMergeSpecOfEnv A lim
      (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps)
      (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps) with
    pre := fun (x, st) s =>
      ⌜tlb_ChunkedCt1AcknowledgedDom x⌝ ∗
        (chunkedCt1AcknowledgedMergeSpecOfEnv A lim
          (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps)
          (tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps)).pre (x, st) s }

private def e2b307_domLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Acknowledged) (bs cur : List (BitVec 8)) : SepProp :=
  chunkedCt1AcknowledgedPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    A.pool lim (M.stepEvents evs st) s ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

section DomSteps

set_option quotPrecheck false in
local notation "entry" => (blkPl_307).base

private theorem e2b307_dom_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) (st : M.σ) (x : ChunkedCt1AcknowledgedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct1Acknowledged) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedCt1AcknowledgedDom x)
    (hsome : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 388717 2560 evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2b307_domSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2b307_domSpec, chunkedCt1AcknowledgedMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  have hpool : A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜tlb_ChunkedCt1AcknowledgedGuardedEnvOf maxOps x evs'⌝ ∗
        A.pool lim (M.stepEvents evs' st) sf := by
    refine Entails.trans ?_ (Entails.sepExists_intro evs)
    rw [A.pool_of_vmPreserved hvm]
    exact Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _)
  exact sepConj_mono_right (sepConj_mono hpool
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2b307_dom_exit_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    {x : ChunkedCt1AcknowledgedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Acknowledged} {cur : List (BitVec 8)} {evs : List AllocEvent}
    (hDom : tlb_ChunkedCt1AcknowledgedDom x)
    (hsome : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hevs : SpqrTightEvs maxOps 388717 2560 evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hpc : s.pc = (blkPl_307).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 cur.length)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s
      (e2b307_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : cur.length = cur.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b307_domLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedSavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    wp_steps
    apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 cur.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - cur.length)) ∗ (curPtr ↦ₛ cur) ⊢
        sliceCursorAfter x.slot x.ptr x.bs cur := by
      rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      exact Entails.of_eq (by dsimp only [curPtr]; sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt s0.sp chunkedMergeStack ∗
        (chunkedCt1AcknowledgedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s)))
      by sep_ac_rfl))
      (e2b307_dom_ok_exit_entails A lim maxOps st x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b307_dom_decode_key_known [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1AcknowledgedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Acknowledged} {cur rest : List (BitVec 8)}
    {evs : List AllocEvent} {key : BitVec 64} {iwt : WireType} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560))
    (hevs : SpqrTightEvs maxOps 388717 2560 evs)
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_307).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s'
        (e2b307_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_307).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s
      (e2b307_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b307_domLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq,
            arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (e2b307_fitsEnv_decodeVarint2_of_some hd hevs hFitTight))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 244#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hnil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hd hevs_dv
      subst hnil
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt1AcknowledgedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b307_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (Entails.of_eq (by
          dsimp only [e2b307_domLoopPre, AllocCostModel.stepEvents, List.foldl]
          sep_ac_rfl))
      refine hcont _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm, hrunm]
      · simp only [arm64_norm, wp_norm, hspm]
      · simp only [arm64_norm, wp_norm, htrm, htr]
      · simp only [arm64_norm, wp_norm, hsm1, hand_wt]
      · simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]
      · simp only [arm64_norm, wp_norm, hx19_m]
      · simp only [arm64_norm, wp_norm, hx20_m]
      · simp only [arm64_norm, wp_norm, hx21_m]
      · simp only [arm64_norm, wp_norm, hx22_m]
      · simp only [arm64_norm, wp_norm, hx23_m]
      · simp only [arm64_norm, wp_norm, hx24_m]
      · simp only [arm64_norm, wp_norm, hx25_m]
      · simp only [arm64_norm, wp_norm, hx26_m]
      · simp only [arm64_norm, wp_norm, hx27_m]
      · simp only [arm64_norm, wp_norm, hx28_m]
      · simp only [arm64_norm, wp_norm, hvregs_m]

private theorem e2b307_dom_tag1_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps maxOps : Nat} (hOps : ucOps ≤ maxOps)
    {H : String → Option (State → State)}
    (hUcTightCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucCt1SentMergeTightSpecOfEnv A lim
          (tlb_UcCt1SentGuardedEnvOf ucOps) (tlb_UcCt1SentGuardedEnvOf ucOps))))
    {x : ChunkedCt1AcknowledgedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {u : V1State.Unchunked.Ct1Sent} {after_uc : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hValidU : tlb_ValidUcCt1SentPB u)
    (hu_lt64 : (V1State.Unchunked.Ct1Sent.encodeRaw u).length < 2 ^ 64)
    (hrest_le : (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc).length ≤ x.bs.length)
    (hrest_lt : (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc).length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc))
    (hcont : ∀ (evs_u : List AllocEvent) (s' : State),
      SpqrTightEvs ucOps 46102 2560 evs_u →
      after_uc.length ≤ x.bs.length → IsDropSuffix x.bs after_uc →
      s'.pc = (blkPl_307).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s'
        (e2b307_domLoopPre A lim st evs_u s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { (default : V1State.Chunked.Ct1Acknowledged) with uc := some u } x.bs after_uc)
        (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_307).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s
      (e2b307_domLoopPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr
        default x.bs (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc))
      (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let rest := tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_uc : UnchunkedCt1SentMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, restPtr, rest⟩
  have hDomUc : tlb_UcCt1SentDom x_uc := ⟨rfl, rfl, u, after_uc, hValidU, rfl⟩
  have huc_ok : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (u, after_uc) :=
    e2b307_mergeMessage_uc hu_lt64
  have huf := proto_mergeMessage_suffix huc_ok
  have hafter_le : after_uc.length ≤ x.bs.length := Nat.le_trans huf.1 hrest_le
  have hafter_suf : IsDropSuffix x.bs after_uc := suffix_trans hrest_le hrest_suf huf.1 huf.2
  apply sepWPpLscro_of_vm (mid := lsmpl.base 312)
  by_vm_steps
    (conv => arg 4; rw [e2b307_domLoopPre, chunkedCt1AcknowledgedPBCapAt,
      show (default : V1State.Chunked.Ct1Acknowledged).uc = none from rfl,
      optUnchunkedCt1SentPBCapAt, memRegion_ct1Sent_none_split x.msgPtr,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_unchunked s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro w120; apply SepWP.exists_elim; intro w72
    apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
    apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
    wp_steps
    apply SepWP.fold (e2b307_default_ct1Sent_entails_zeroCap A.repAlloc x.msgPtr) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_uc, st))
      (ret_pc := entry + 356#64) hUcTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [tlb_ucCt1SentMergeTightSpecOfEnv, x_uc]
            rw [tlb_domHeap_of_dom hDomUc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, AllocCostModel.stepEvents, List.foldl,
              arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        e2b307_fitsEnv_uc_of_dom hOps hDomUc hFitTight⟩)
      (by dsimp only [AllocCostModel.stepEvents, List.foldl, restPtr, rest]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_ucCt1SentMergeTightSpecOfEnv, unchunkedCt1SentMergeSpecOfEnv,
        x_uc, huc_ok, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_u
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_u_g
      wp_focus_pure; intro hsm0
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      have hevs_u : SpqrTightEvs ucOps 46102 2560 evs_u :=
        e2b307_tight_of_guarded_dom hDomUc hevs_u_g
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf huf.1)
        (by dsimp only [rest]; sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b307_domLoopPre A lim st evs_u s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { (default : V1State.Chunked.Ct1Acknowledged) with uc := some u } x.bs after_uc)
        (Entails.of_eq (by
          dsimp only [e2b307_domLoopPre, chunkedCt1AcknowledgedPBCapAt,
            optUnchunkedCt1SentPBCapAt]
          rw [chunkedBelow_eq_unchunked]
          sep_ac_rfl))
      exact hcont evs_u _ hevs_u hafter_le hafter_suf
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

private theorem e2b307_dom_tag2_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {H : String → Option (State → State)}
    (hDecTightCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps))))
    {x : ChunkedCt1AcknowledgedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.Ct1Sent} {d : PolynomialDecoder}
    {tail : List (BitVec 8)} {evs_u : List AllocEvent} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560))
    (hevs_u : SpqrTightEvs ucOps 46102 2560 evs_u)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hValidD : tlb_ValidPolyDecoderPB d)
    (hd_lt64 : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64)
    (hrest_le : (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail).length ≤ x.bs.length)
    (hrest_lt56 : (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail).length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail))
    (hcont : ∀ (evs : List AllocEvent) (s' : State),
      SpqrTightEvs maxOps 388717 2560 evs →
      tail.length ≤ x.bs.length → IsDropSuffix x.bs tail →
      s'.pc = (blkPl_307).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s'
        (e2b307_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, receivingEk := some d } x.bs tail)
        (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_307).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s
      (e2b307_domLoopPre A lim st evs_u s0 s x.msgPtr x.bufRef x.slot x.ptr
        { uc := ucOpt, receivingEk := none } x.bs
        (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail))
      (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let rest := tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyDecoderMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr + 128#64, default, x.bufRef, x.slot, restPtr, rest⟩
  have hDomDec : tlb_PolyDecoderDom x_poly := ⟨rfl, rfl, d, tail, hValidD, rfl⟩
  have hpe_ok : (mergeMessage PolynomialDecoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (d, tail) :=
    e2b307_mergeMessage_polyDec hd_lt64
  have hpf := proto_mergeMessage_suffix hpe_ok
  have htail_le : tail.length ≤ x.bs.length := Nat.le_trans hpf.1 hrest_le
  have htail_suf : IsDropSuffix x.bs tail := suffix_trans hrest_le hrest_suf hpf.1 hpf.2
  apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
  by_vm_steps
    (conv => arg 4; rw [e2b307_domLoopPre, chunkedCt1AcknowledgedPBCapAt,
      optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (x.msgPtr + 128#64),
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_eq_poly s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
    apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
    wp_steps
    apply SepWP.fold (e2b307_default_polyDecoder_entails_zeroCap A.repAlloc (x.msgPtr + 128#64))
      (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs_u st))
      (ret_pc := entry + 296#64) hDecTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [tlb_polyDecoderMergeTightSpecOfEnv, x_poly]
            rw [tlb_domHeap_of_dom hDomDec]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        by change ([] : List (List (BitVec 8))).length + rest.length < 2 ^ 56;
           simpa using hrest_lt56,
        e2b307_fitsEnv_polyDec_of_dom hOps hDomDec hevs_u hFitTight⟩)
      (by dsimp only [restPtr, rest]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv, polyDecoderMergeSpecOfEnv,
        x_poly, hpe_ok, hsp, protoPolynomialDecoderAt_eq_pb,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_d
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_d_g
      wp_focus_pure; intro hsm0
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      have hevs_d : SpqrTightEvs decOps 342615 2560 evs_d :=
        e2b307_tight_of_guarded_dom hDomDec hevs_d_g
      have hevs_all : SpqrTightEvs maxOps 388717 2560 (evs_u ++ evs_d) :=
        (hevs_u.append hevs_d).mono hOps (by decide) (by decide)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hpf.1)
        (by dsimp only [rest]; sep_focus)
      apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A.repAlloc x.msgPtr ucOpt hpf.1)
        (by dsimp only [rest]; sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← M.stepEvents_append, ← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b307_domLoopPre A lim st (evs_u ++ evs_d) s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, receivingEk := some d } x.bs tail)
        (Entails.of_eq (by
          dsimp only [e2b307_domLoopPre, chunkedCt1AcknowledgedPBCapAt,
            optPolynomialDecoderPBAt]
          rw [chunkedBelow_eq_poly]
          sep_ac_rfl))
      exact hcont (evs_u ++ evs_d) _ hevs_all htail_le htail_suf
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

private theorem e2b307_dom_blk_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucCt1SentMergeTightSpecOfEnv A lim
          (tlb_UcCt1SentGuardedEnvOf ucOps) (tlb_UcCt1SentGuardedEnvOf ucOps))))
    (hDecTightCall : subroutine_ok ((blkPC_307).rebase (blkPl_307).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_307).rebase (blkPl_307).base H)
      (blkPl_307).base
      (withLsCodeRoLoaded lsmpl (e2b307_domSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b307_domSpec chunkedCt1AcknowledgedMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  intro hDom
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, hpts_0, hFit⟩
  have hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 388717 2560) :=
    fun evs ht => hFit evs (Or.inl ⟨hDom, ht⟩)
  rcases hDom with ⟨hwt_c, hmsg, pb, tail, hpb, hbs⟩
  have hwt_ld : x.wt = .lengthDelimited := e2b307_wt_eq_ld hwt_c
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  let raw := V1State.Chunked.Ct1Acknowledged.encodeRaw pb
  let rest0 := raw ++ tail
  have hraw_le_bs : raw.length + tail.length ≤ x.bs.length := by
    have h1 : x.bs.length =
        (encodeVarint (BitVec.ofNat 64 raw.length)).length + raw.length + tail.length := by
      simp [hbs, tlb_lenPrefixed, raw, List.length_append]
      omega
    omega
  have hraw_lt64 : raw.length < 2 ^ 64 := by omega
  have hlen_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat]; omega
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, rest0) := by
    rw [hbs, tlb_lenPrefixed, List.append_assoc]
    exact e2b307_decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) rest0
  have hsome_top : (mergeMessage V1State.Chunked.Ct1Acknowledged.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail) := by
    rw [hmsg, hbs]
    exact e2b307_mergeMessage_top_dom hwt_c hraw_lt64
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hlt_len : ¬ rest0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_toNat]; dsimp only [rest0]; simp only [List.length_append]; omega
  have hlim_eq : rest0.length - raw.length = tail.length := by
    dsimp only [rest0]; simp only [List.length_append]; omega
  have hule := ule_len_of_ge hlt_len hrest0_lt
  have hsub := bv_len_sub_limit hlt_len
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        memRegion (s0.sp - 56#64) 8 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedSavedRegs s0 := Entails.refl _
  have hPhase2 : ∀ (evs_u : List AllocEvent) (s1 : State),
      SpqrTightEvs ucOps 46102 2560 evs_u →
      (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail).length ≤ x.bs.length →
      IsDropSuffix x.bs (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail) →
      s1.pc = entry + 192#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 tail.length →
      ChunkedLoopRegs s0 s1 →
      SepWPpLscro lsmpl ((blkPC_307).rebase (blkPl_307).base H) (s0.readReg64 Reg.lr) s1
        (e2b307_domLoopPre A lim st evs_u s0 s1 x.msgPtr x.bufRef x.slot x.ptr
          { uc := pb.uc, receivingEk := none } x.bs
          (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail))
        (WppPost (e2b307_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro evs_u s1 hevs_u hafter_le hafter_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
    have hDom_full : tlb_ChunkedCt1AcknowledgedDom x := ⟨hwt_c, hmsg, pb, tail, hpb, hbs⟩
    rcases hd_opt : pb.receivingEk with _ | d
    · rw [hd_opt] at hafter_le hafter_suf
      have hm_eq : ({ uc := pb.uc, receivingEk := none } : V1State.Chunked.Ct1Acknowledged) = pb := by
        cases pb; dsimp only at hd_opt; subst hd_opt; rfl
      have hcur_eq : encodeOptMessage PolynomialDecoder.encodeRaw 2#32 none ++ tail = tail := rfl
      rw [hcur_eq] at hafter_le hafter_suf ⊢
      rw [hm_eq]
      exact e2b307_dom_exit_step hDom_full hsome_top
        (hevs_u.mono (by omega) (by decide) (Nat.le_refl 2560))
        hsp_align hafter_le hafter_suf hpc1 hrun1 hsp1 htr1 hx21_1 hx22_1 hcs1
    · rw [hd_opt] at hafter_le hafter_suf
      have hValidD : tlb_ValidPolyDecoderPB d := hpb.2 d hd_opt
      let rest2 := tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) tail
      have hcur2_eq : encodeOptMessage PolynomialDecoder.encodeRaw 2#32 (some d) ++ tail =
          encodeVarint 18#64 ++ rest2 := e2b307_encodeOpt_dec_some d tail
      rw [hcur2_eq] at hafter_le hafter_suf ⊢
      have hgt2 : ¬ (encodeVarint 18#64 ++ rest2).length ≤ tail.length := by
        have hv : encodeVarint 18#64 = [18#8] := by decide
        simp only [hv, rest2, tlb_lenPrefixed, List.length_append, List.length_cons, List.length_nil]
        omega
      have hd2 : decodeVarint (encodeVarint 18#64 ++ rest2) = some (18#64, rest2) :=
        e2b307_decodeVarint_encodeVarint 18#64 rest2
      have hrest2_le_cur : rest2.length ≤ (encodeVarint 18#64 ++ rest2).length :=
        Nat.le_of_lt (decodeVarint_length hd2)
      have hrest2_le : rest2.length ≤ x.bs.length := Nat.le_trans hrest2_le_cur hafter_le
      have hrest2_lt56 : rest2.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest2_le hbs_lt56
      have hrest2_suf : IsDropSuffix x.bs rest2 :=
        suffix_trans hafter_le hafter_suf hrest2_le_cur (decodeVarint_suffix hd2)
      have hd_lt64 : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64 := by
        have hlen2 : rest2.length =
            (encodeVarint (BitVec.ofNat 64 (PolynomialDecoder.encodeRaw d).length)).length +
              (PolynomialDecoder.encodeRaw d).length + tail.length := by
          simp [rest2, tlb_lenPrefixed, List.length_append]
          omega
        omega
      refine e2b307_dom_decode_key_known hVarintCall hFitTight
        (hevs_u.mono (by omega) (by decide) (Nat.le_refl 2560))
        hgt2 hsp_align hafter_le (Nat.lt_of_le_of_lt hafter_le hbs_lt) hafter_suf
        hd2 (by decide) (by decide : WireType.ofNat? ((18#64).toNat % 8) = some .lengthDelimited)
        (by decide) ?_ hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
      intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
      refine e2b307_dom_tag2_some_step hOps hDecTightCall hFitTight hevs_u hsp_align
        hValidD hd_lt64 hrest2_le hrest2_lt56 hrest2_suf ?_
        hpc2 hrun2 hsp2 htr2 hx0_2
        (by simpa using hx1_2) hx19_2 hx20_2 hx21_2 hx22_2 hcs2
      intro evs s3 hevs htail_le htail_suf hpc3 hrun3 hsp3 htr3 _ _ hx21_3 hx22_3 hcs3
      have hm_eq : ({ uc := pb.uc, receivingEk := some d } : V1State.Chunked.Ct1Acknowledged) = pb := by
        cases pb; dsimp only at hd_opt; subst hd_opt; rfl
      rw [hm_eq]
      exact e2b307_dom_exit_step hDom_full hsome_top hevs hsp_align htail_le htail_suf
        hpc3 hrun3 hsp3 htr3 hx21_3 hx22_3 hcs3
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
    apply SepWP.fold hsaved (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st))
      (ret_pc := entry + 56#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf],
        hbs_lt,
        by simpa only [AllocCostModel.stepEvents, List.foldl] using
             e2b307_fitsEnv_decodeVarint2_of_some hdv0
               (SpqrTightEvs.nil maxOps 388717 2560) hFitTight⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
      at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 192#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hnil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hnil
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt1AcknowledgedPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b307_domLoopPre A lim st [] s0 _ x.msgPtr x.bufRef x.slot x.ptr
          default x.bs rest0)
        (Entails.of_eq (by
          dsimp only [e2b307_domLoopPre, AllocCostModel.stepEvents, List.foldl]
          rw [hmsg, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
          sep_ac_rfl))
      have hrest0_split : rest0 =
          encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 pb.uc ++
            (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail) := by
        dsimp only [rest0, raw, V1State.Chunked.Ct1Acknowledged.encodeRaw]
        rw [List.append_assoc]
      rcases huc_opt : pb.uc with _ | u
      · rw [huc_opt] at hrest0_split
        have hrest0_eq : rest0 =
            encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail := by
          simpa [encodeOptMessage] using hrest0_split
        rw [hrest0_eq] at hrest0_le hrest0_suf ⊢
        have hm0_eq : (default : V1State.Chunked.Ct1Acknowledged) =
            { uc := pb.uc, receivingEk := none } := by
          rw [huc_opt]; rfl
        rw [hm0_eq]
        refine hPhase2 [] _ (SpqrTightEvs.nil ucOps 46102 2560)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
        · simpa [huc_opt] using hrest0_le
        · simpa [huc_opt] using hrest0_suf
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hrunm]
        · simp only [arm64_norm, wp_norm, hspm]
        · simp only [arm64_norm, wp_norm, htrm]
        · simp only [arm64_norm, wp_norm, hx19_m]
        · simp only [arm64_norm, wp_norm, hx20_m]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hx26_m]
        · simp only [arm64_norm, wp_norm, hx27_m]
        · simp only [arm64_norm, wp_norm, hx28_m]
        · simp only [arm64_norm, wp_norm, hvregs_m]
      · have hValidU : tlb_ValidUcCt1SentPB u := hpb.1 u huc_opt
        let after_uc := encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ tail
        let rest1 := tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) after_uc
        have hrest0_eq : rest0 = encodeVarint 10#64 ++ rest1 := by
          rw [hrest0_split, huc_opt]
          exact e2b307_encodeOpt_uc_some u after_uc
        rw [hrest0_eq] at hrest0_le hrest0_lt hrest0_suf ⊢
        have hgt1 : ¬ (encodeVarint 10#64 ++ rest1).length ≤ tail.length := by
          have hv : encodeVarint 10#64 = [10#8] := by decide
          simp only [hv, rest1, after_uc, tlb_lenPrefixed, List.length_append, List.length_cons,
            List.length_nil]
          omega
        have hd1 : decodeVarint (encodeVarint 10#64 ++ rest1) = some (10#64, rest1) :=
          e2b307_decodeVarint_encodeVarint 10#64 rest1
        have hrest1_le_cur : rest1.length ≤ (encodeVarint 10#64 ++ rest1).length :=
          Nat.le_of_lt (decodeVarint_length hd1)
        have hrest1_le : rest1.length ≤ x.bs.length := Nat.le_trans hrest1_le_cur hrest0_le
        have hrest1_lt : rest1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le hbs_lt
        have hrest1_suf : IsDropSuffix x.bs rest1 :=
          suffix_trans hrest0_le hrest0_suf hrest1_le_cur (decodeVarint_suffix hd1)
        have hu_lt64 : (V1State.Unchunked.Ct1Sent.encodeRaw u).length < 2 ^ 64 := by
          have hlen1 : rest1.length =
              (encodeVarint (BitVec.ofNat 64 (V1State.Unchunked.Ct1Sent.encodeRaw u).length)).length +
                (V1State.Unchunked.Ct1Sent.encodeRaw u).length + after_uc.length := by
            simp [rest1, tlb_lenPrefixed, List.length_append]
            omega
          omega
        refine e2b307_dom_decode_key_known hVarintCall hFitTight
          (SpqrTightEvs.nil maxOps 388717 2560)
          hgt1 hsp_align hrest0_le hrest0_lt hrest0_suf
          hd1 (by decide) (by decide : WireType.ofNat? ((10#64).toNat % 8) = some .lengthDelimited)
          (by decide) ?_
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq])
          ⟨by simp only [arm64_norm, wp_norm],
           by simp only [arm64_norm, wp_norm],
           by simp only [arm64_norm, wp_norm],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩
        intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
        refine e2b307_dom_tag1_some_step (by omega) hUcTightCall hFitTight hsp_align
          hValidU hu_lt64 hrest1_le hrest1_lt hrest1_suf ?_
          hpc1 hrun1 hsp1 htr1 hx0_1
          (by simpa using hx1_1) hx19_1 hx20_1 hx21_1 hx22_1 hcs1
        intro evs_u s2 hevs_u hafter_le hafter_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2
        have hm1_eq : ({ (default : V1State.Chunked.Ct1Acknowledged) with uc := some u }) =
            { uc := pb.uc, receivingEk := none } := by
          rw [huc_opt]; rfl
        rw [hm1_eq]
        exact hPhase2 evs_u s2 hevs_u hafter_le hafter_suf
          hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hcs2

end DomSteps

/-! ## 4. Exported Guarded-Tight Placed Contracts (`e2b307_`) -/

/-- Block `307` (`V1State.Chunked.Ct1Acknowledged::merge`) guarded-tight placed contract,
parametric in `ucOps decOps maxOps : Nat` (`hOps : ucOps + decOps ≤ maxOps`), using an explicit
own-block untightened `hFallback` for `¬ tlb_ChunkedCt1AcknowledgedDom x`. -/
theorem e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim))) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim maxOps ext := by
  unfold tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hfr0.1 307 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  by_cases hDom : tlb_ChunkedCt1AcknowledgedDom x
  · have hDomOwn := e2b307_own_of_blk_cro (e2b307_dom_blk_ok A lim hOps
      (e2b307_lift_cl_of_own hVarint)
      (e2b307_lift_cro_of_own hUcTight)
      (e2b307_lift_cro_of_own hDecTight))
    have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (e2b307_domSpec A lim maxOps)).pre (x, st) s0 ∗ R :=
      Satisfies.of_entails hpre (sepConj_mono_left
        (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _))))
    obtain ⟨sf, hsteps, hout, _⟩ := hDomOwn.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_dom hsp hQL
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  · have hpre_fb : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim)).pre (x, st) s0 ∗ R := by
      refine Satisfies.of_entails hpre (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedCt1AcknowledgedMergeSpec,
        chunkedCt1AcknowledgedMergeSpecOfEnv]
      refine sepConj_mono_left ?_
      exact Entails.pure_left fun ⟨h0, h1, h2, h3, hFit⟩ =>
        Entails.pure_right ⟨h0, h1, h2, h3, tlb_fitsEnv_fallback_of_not_dom hDom hFit⟩
          (Entails.refl _)
    obtain ⟨sf, hsteps, hout, _⟩ := hFallback.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_fb hsp hQL
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, hp⟩ | ⟨hoom, hp⟩
    · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
      refine Satisfies.of_entails hpost (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedCt1AcknowledgedMergeSpec,
        chunkedCt1AcknowledgedMergeSpecOfEnv]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      refine Entails.sepExists_elim fun evs => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro evs)
      exact Entails.pure_left fun hevs =>
        Entails.pure_right (Or.inr ⟨hDom, chunkedCt1AcknowledgedMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _)
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hp⟩)))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inl ⟨code, hex, hp⟩))))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inr ⟨hoom, hp⟩))))

/-- Block `307` (`V1State.Chunked.Ct1Acknowledged::merge`) guarded-tight placed contract,
parametric in `ucOps decOps maxOps : Nat` (`hOps : ucOps + decOps ≤ maxOps`), deriving the
`¬ tlb_ChunkedCt1AcknowledgedDom x` fallback from the standard own-block callee contracts
(`261, 257, 291, 263, 312, 296`) via `chunkedCt1Acknowledged_merge_cl_placed_ok_of_contracts`. -/
theorem e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ucOps decOps maxOps : Nat} (hOps : ucOps + decOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUc312Base : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOkOf A lim ucOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOkOf A lim maxOps ext :=
  e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_fallback A lim hOps hVarint
    hUcTight hDecTight
    (e2b307_own_of_blk_cro (chunked_ct1_acknowledged_merge_cl_placed_ok_of_contracts
      (e2b307_lift_cl_of_own hFrom) (e2b307_lift_cl_of_own hPush)
      (e2b307_lift_cl_of_own hVarint) (e2b307_lift_cl_of_own hSkip)
      (e2b307_lift_cro_of_own hUc312Base) (e2b307_lift_cro_of_own hPolyDecBase)))

/-- Default `2`-op-per-`bytes` instantiation (`ucOps = 10`, `decOps = 35`, `maxOps = 45`) of
`e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_fallback`. -/
theorem e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_default_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOk A lim ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOk A lim ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 307 (Rust.withPanics ext))
      (lsmpl.base 307) (withLsCodeRoLoaded lsmpl (chunkedCt1AcknowledgedMergeSpec A lim))) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOk A lim ext :=
  e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_fallback A lim (by decide : 10 + 35 ≤ 45)
    hVarint hUcTight hDecTight hFallback

/-- Default `2`-op-per-`bytes` instantiation (`ucOps = 10`, `decOps = 35`, `maxOps = 45`) of
`e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_contracts`. -/
theorem e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_default_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUc312Base : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312) (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcCt1SentMergePlacedTightOk A lim ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOk A lim ext) :
    tlb_ChunkedCt1AcknowledgedMergePlacedTightOk A lim ext :=
  e2b307_chunkedCt1AcknowledgedMerge_placed_tight_ok_of_contracts A lim (by decide : 10 + 35 ≤ 45)
    hFrom hPush hVarint hSkip hUc312Base hPolyDecBase hUcTight hDecTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB307PlacedBudget
