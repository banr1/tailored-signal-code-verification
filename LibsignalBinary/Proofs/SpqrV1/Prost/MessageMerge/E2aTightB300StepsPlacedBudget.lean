/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Step Proofs for `Chunked.Ct1Sampled::merge` (Block `300`)

Provides canonical `tlb_ChunkedCt1SampledDom` codec round-trip lemmas, zero-capacity initialization
folds (`cap = 0#64`), loop-head invariant `e2ka_b300TightPre`, and per-field tight budget step
lemmas (`uc`, `sendingEk`, `receivingCt2`, and exit) for `Chunked.Ct1Sampled::merge` on Block `300`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300StepsPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix itag_beq_tag_false
   key_shr32_of_lt key_wt_some sf_truncate32_ofNat64
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeKey encodeMessage encodeOptMessage encodeVarint encodeVarintAux mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderAt protoPolynomialDecoderPinnedAt
   protoPolynomialEncoderAt protoPolynomialEncoderPinnedAt
   protoPolynomialEncoderPolysOff vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (optPolynomialDecoderPBAt optPolynomialEncoderPBAt
   vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1SampledMergeGhost ChunkedLoopRegs PolyDecoderMergeGhost
   PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedBelow_eq_poly chunkedBelow_eq_unchunked
   chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedCt1SampledMerge_fnOff chunkedCt1SampledPBCapAt
   chunkedCt1SampledPBCapAt_mono chunkedMergeStack chunkedSavedRegs
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   memRegion_ct1Sent_none_split memRegion_polyDecoder_none_split
   memRegion_polyEncoder_none_split
   optUnchunkedCt1SentPBCapAt optUnchunkedCt1SentPBCapAt_mono
   pointsTo64_zero_eq_pointsTo32_pair
   polyDecoderToProto polyEncoderToProto protoPolynomialDecoderAt_eq_pb
   protoPolynomialEncoderAt_eq_pb proto_mergeMessage_suffix setWidth8_ofNat64_wt
   unchunkedCt1SentPBCapAt vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_300 blkPl_300)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedCt1SampledDom tlb_ChunkedCt1SampledGuardedEnvOf
   tlb_ChunkedCt1SampledTightEnvOf
   tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderTightEnvOf
   tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf tlb_PolyEncoderTightEnvOf
   tlb_UcCt1SentDom tlb_UcCt1SentGuardedEnvOf tlb_UcCt1SentTightEnvOf
   tlb_ValidPolyDecoderPB tlb_ValidPolyEncoderPB tlb_ValidUcCt1SentPB
   tlb_domHeap_of_dom tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom
   tlb_lenPrefixed tlb_polyDecoderMergeTightSpecOfEnv tlb_polyDecoderZeroCapAt
   tlb_polyDecoderZeroCapAt_of_ptr tlb_polyEncoderMergeTightSpecOfEnv
   tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs
   tlb_ucCt1SentMergeTightSpecOfEnv tlb_ucCt1SentZeroCapAt
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (stackAt_chunkedMerge_epilogue stackAt_decodeVarint2_raw_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1SampledMergePostEnv UnchunkedCt1SentMergePostEnv
   chunkedCt1SampledMergeSpecOfEnv unchunkedCt1SentMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergePostEnv PolyEncoderMergePostEnv
   polyDecoderMergeSpecOfEnv polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
  chunkedCt1SampledMerge_fnOff setWidth8_ofNat64_wt

/-! ## 1. Pure Tight-Budget, Codec & Zero-Cap Initialization Helpers -/

theorem e2ka_stepEvents_append {M : AllocCostModel} (evs₁ evs₂ : List AllocEvent) (st : M.σ) :
    M.stepEvents (evs₁ ++ evs₂) st = M.stepEvents evs₂ (M.stepEvents evs₁ st) := by
  unfold AllocCostModel.stepEvents
  exact List.foldl_append

theorem e2ka_fitsEnv_step_suffix {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {ETotal ESub : List AllocEvent → Prop} {evsPre : List AllocEvent}
    (hFit : FitsEnv M lim st ETotal)
    (hSub : ∀ evs, ESub evs → ETotal (evsPre ++ evs)) :
    FitsEnv M lim (M.stepEvents evsPre st) ESub :=
  fun evs hs =>
    ((LibsignalBinary.Heap.fitsEvents_append M lim evsPre evs st).mp
      (hFit (evsPre ++ evs) (hSub evs hs))).2

theorem e2ka_b300_tightEnv_combine {ucOps encOps decOps maxOps : Nat}
    {evsUc evsEnc evsDec : List AllocEvent}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hUc : tlb_UcCt1SentTightEnvOf ucOps evsUc)
    (hEnc : tlb_PolyEncoderTightEnvOf encOps evsEnc)
    (hDec : tlb_PolyDecoderTightEnvOf decOps evsDec) :
    tlb_ChunkedCt1SampledTightEnvOf maxOps (evsUc ++ evsEnc ++ evsDec) :=
  ((SpqrTightEvs.append hUc hEnc).append hDec).mono hOps (by decide) (by decide)

theorem e2ka_decodeVarint_encodeVarint (v : BitVec 64) (rest : List (BitVec 8)) :
    decodeVarint (encodeVarint v ++ rest) = some (v, rest) := by
  rw [← proto_decodeVarint_toOption]
  rw [CryptoVerification.SpqrV1Sync.Codec.proto_decodeVarint_encodeVarint v rest]
  rfl

theorem e2ka_decodeVarint_lenPrefixed (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) = some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  exact e2ka_decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)

theorem e2ka_lenPrefixed_raw_le (raw rest : List (BitVec 8)) :
    raw.length ≤ (tlb_lenPrefixed raw rest).length := by
  unfold tlb_lenPrefixed
  simp only [List.length_append]
  omega

theorem e2ka_encodeOptMessage_some_append {N : Type} (enc : N → List (BitVec 8))
    (tag : BitVec 32) (n : N) (next : List (BitVec 8)) :
    encodeOptMessage enc tag (some n) ++ next =
      encodeKey tag .lengthDelimited ++ tlb_lenPrefixed (enc n) next := by
  simp only [encodeOptMessage, encodeMessage, tlb_lenPrefixed, List.append_assoc]

theorem e2ka_decodeVarint_key1 (rest : List (BitVec 8)) :
    decodeVarint (encodeKey 1#32 .lengthDelimited ++ rest) = some (0x0a#64, rest) := by
  have hk : encodeKey 1#32 .lengthDelimited = encodeVarint 0x0a#64 := rfl
  rw [hk]
  exact e2ka_decodeVarint_encodeVarint 0x0a#64 rest

theorem e2ka_decodeVarint_key2 (rest : List (BitVec 8)) :
    decodeVarint (encodeKey 2#32 .lengthDelimited ++ rest) = some (0x12#64, rest) := by
  have hk : encodeKey 2#32 .lengthDelimited = encodeVarint 0x12#64 := rfl
  rw [hk]
  exact e2ka_decodeVarint_encodeVarint 0x12#64 rest

theorem e2ka_decodeVarint_key3 (rest : List (BitVec 8)) :
    decodeVarint (encodeKey 3#32 .lengthDelimited ++ rest) = some (0x1a#64, rest) := by
  have hk : encodeKey 3#32 .lengthDelimited = encodeVarint 0x1a#64 := rfl
  rw [hk]
  exact e2ka_decodeVarint_encodeVarint 0x1a#64 rest

theorem e2ka_encodeKey_pos (tag : BitVec 32) (rest : List (BitVec 8)) :
    rest.length < (encodeKey tag .lengthDelimited ++ rest).length := by
  simp only [encodeKey, encodeVarint, encodeVarintAux, List.length_append]
  split <;> simp

theorem e2ka_lenPrefixed_ge_tail (raw next : List (BitVec 8)) :
    next.length ≤ (tlb_lenPrefixed raw next).length := by
  unfold tlb_lenPrefixed
  simp only [List.length_append]
  omega

theorem e2ka_mergeMessage_ct1Sampled_ok (pb : V1State.Chunked.Ct1Sampled)
    (tail : List (BitVec 8))
    (hlen : (V1State.Chunked.Ct1Sampled.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.Ct1Sampled.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.Ct1Sampled.encodeRaw pb) tail) 99).toOption =
      some (pb, tail) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  have h := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Chunked.Ct1Sampled.mergeField 2 V1State.Chunked.Ct1Sampled.encodeRaw
    default pb 99 tail
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_ch_ct1Sampled pb hlen) hlen (by decide)
  exact congrArg Except.toOption h

theorem e2ka_mergeMessage_ucCt1Sent_ok (u : V1State.Unchunked.Ct1Sent)
    (next : List (BitVec 8))
    (hlen : (V1State.Unchunked.Ct1Sent.encodeRaw u).length < 2 ^ 64) :
    (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) next) 98).toOption =
      some (u, next) := by
  unfold tlb_lenPrefixed codecWireTypeToProto
  rw [List.append_assoc]
  have h := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Unchunked.Ct1Sent.mergeField 1 V1State.Unchunked.Ct1Sent.encodeRaw
    default u 98 next
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_uc_ct1Sent u hlen) hlen (by decide)
  exact congrArg Except.toOption h

theorem e2ka_mergeMessage_polyEncoder_ok (pe : PolynomialEncoder)
    (next : List (BitVec 8))
    (hlen : (PolynomialEncoder.encodeRaw pe).length < 2 ^ 64) :
    (mergeMessage PolynomialEncoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (PolynomialEncoder.encodeRaw pe) next) 98).toOption =
      some (pe, next) := by
  unfold tlb_lenPrefixed codecWireTypeToProto
  rw [List.append_assoc]
  have h := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw
    default pe 98 next
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyEncoder pe hlen) hlen (by decide)
  exact congrArg Except.toOption h

theorem e2ka_mergeMessage_polyDecoder_ok (pd : PolynomialDecoder)
    (next : List (BitVec 8))
    (hlen : (PolynomialDecoder.encodeRaw pd).length < 2 ^ 64) :
    (mergeMessage PolynomialDecoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (PolynomialDecoder.encodeRaw pd) next) 98).toOption =
      some (pd, next) := by
  unfold tlb_lenPrefixed codecWireTypeToProto
  rw [List.append_assoc]
  have h := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw
    default pd 98 next
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyDecoder pd hlen) hlen (by decide)
  exact congrArg Except.toOption h

private theorem e2ka_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2ka_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecVecU8PinnedAt A (VecPin.mk 0#64 ptr) a [] := by
  unfold vecVecU8PinnedAt CryptoVerification.RustHeap.vecAt vecHeader vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat * CryptoVerification.SpqrV1.Poly.vecHeaderBytes < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  exact Entails.pure_right hp (Entails.refl _)

theorem e2ka_default_ct1Sent_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
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
  have h1 := e2ka_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2ka_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h3 := e2ka_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 48#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_lin
  have h64 : a + 48#64 + 16#64 = a + 64#64 := by bv_lin
  have h80 : a + 72#64 + 8#64 = a + 80#64 := by bv_lin
  rw [h32, h40] at h2; rw [h56, h64] at h3; rw [h80]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _))))

theorem e2ka_default_polyEncoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + 24#64) [] ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := e2ka_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h2 := e2ka_pointsTo_zero_entails_vecVecU8ZeroPin A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

theorem e2ka_default_polyDecoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7 ⊢
      tlb_polyDecoderZeroCapAt A p (polyDecoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyDecoderZeroCapAt_of_ptr A 8#64 p (polyDecoderToProto default))
  unfold protoPolynomialDecoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    ((p + 24#64) ↦₃₂ 0#32) ∗ ((p + 28#64) ↦₃₂ 0#32) ∗
    ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7
  have h1 := e2ka_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
  rw [pointsTo64_zero_eq_pointsTo32_pair (p + 24#64), h28]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

/-! ## 2. Concrete-Pool Loop-Head Invariant & Step Lemmas on `tlb_ChunkedCt1SampledDom` -/

def e2ka_b300TightPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evsAcc : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.Ct1Sampled) (bs cur : List (BitVec 8)) : SepProp :=
  A.pool lim (M.stepEvents evsAcc st) s ∗
    chunkedCt1SampledPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

abbrev e2ka_b300TightSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedCt1SampledMergeGhost × M.σ) :=
  chunkedCt1SampledMergeSpecOfEnv A lim
    (tlb_ChunkedCt1SampledGuardedEnvOf maxOps)
    (tlb_ChunkedCt1SampledGuardedEnvOf maxOps)

section Steps

set_option quotPrecheck false in
local notation "entry" => (blkPl_300).base

@[local simp, local arm64_norm]
private theorem e2ka_iwt_w0_trunc32_zext64_setWidth8 (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

/-- Canonical key-decode step at `entry + 192#64` → `entry + 244#64` when `decodeVarint cur`
succeeds on a valid `1 ≤ tag < 2^29` field key (`0` allocator events). -/
theorem e2ka_b300_decode_key_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {evsAcc : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {iwt : WireType} {limit : Nat}
    (hFitTight : FitsEnv M lim st (tlb_ChunkedCt1SampledTightEnvOf maxOps))
    (hAcc : tlb_ChunkedCt1SampledTightEnvOf maxOps evsAcc)
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag_ge1 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_300).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (e2ka_b300TightPre A lim st evsAcc s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (e2ka_b300TightPre A lim st evsAcc s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2ka_b300TightPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evsAcc st))
      (ret_pc := entry + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq,
            arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt
        (e2ka_fitsEnv_step_suffix hFitTight fun evs h => by
          rw [decodeVarint2Env_eq_nil_of_some hd h, List.append_nil]
          exact hAcc))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m,
            hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m
         hx26_m hx27_m hx28_m hvregs_m
    have hshr := key_shr32_of_lt hk_lt
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag_ge1
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := entry + 244#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hd hevs_dv
      subst hevs_nil
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      have hst_eq : M.stepEvents [] (M.stepEvents evsAcc st) = M.stepEvents evsAcc st := rfl
      rw [hst_eq, ← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2ka_b300TightPre A lim st evsAcc s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2ka_b300TightPre]; sep_entail)
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

/-- Field 1 (`uc : Option Unchunked.Ct1Sent`, Tag `1`, starting from `default`):
advances `cur = Proto.encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 pbUc ++ cur₁` to
`cur₁` with `evsUc` satisfying `tlb_UcCt1SentTightEnvOf ucOps evsUc`. -/
theorem e2ka_b300_opt1_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucCt1SentMergeTightSpecOfEnv A lim
          (tlb_UcCt1SentGuardedEnvOf ucOps) (tlb_UcCt1SentGuardedEnvOf ucOps))))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {pbUc : Option V1State.Unchunked.Ct1Sent} {cur cur₁ : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (tlb_ChunkedCt1SampledTightEnvOf maxOps))
    (hValUc : ∀ u, pbUc = some u → tlb_ValidUcCt1SentPB u)
    (hcur_eq : cur = encodeOptMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 pbUc ++ cur₁)
    (hlim_le_cur1 : limit ≤ cur₁.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ (evsUc : List AllocEvent) (s' : State),
      tlb_UcCt1SentTightEnvOf ucOps evsUc →
      cur₁.length ≤ x.bs.length → IsDropSuffix x.bs cur₁ →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (e2ka_b300TightPre A lim st evsUc s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc } x.bs cur₁)
        (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (e2ka_b300TightPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs cur)
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases pbUc with _ | u
  · have hcur1 : cur = cur₁ := by simpa [encodeOptMessage] using hcur_eq
    subst hcur1
    have hm_eq :
        ({ (default : V1State.Chunked.Ct1Sampled) with uc := none } : V1State.Chunked.Ct1Sampled) =
          default := rfl
    refine SepWPpLscro.weaken_pre
      (P' := e2ka_b300TightPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr
        { (default : V1State.Chunked.Ct1Sampled) with uc := none } x.bs cur)
      (by rw [hm_eq]; exact Entails.refl _) ?_
    exact hcont [] s (SpqrTightEvs.nil ucOps 46102 2560) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
  · let rest₁ := tlb_lenPrefixed (V1State.Unchunked.Ct1Sent.encodeRaw u) cur₁
    have hcur_key : cur = encodeKey 1#32 .lengthDelimited ++ rest₁ := by
      rw [hcur_eq]
      exact e2ka_encodeOptMessage_some_append V1State.Unchunked.Ct1Sent.encodeRaw 1#32 u cur₁
    have hcur1_le_rest1 : cur₁.length ≤ rest₁.length := e2ka_lenPrefixed_ge_tail _ _
    have hrest1_lt_cur : rest₁.length < cur.length := by
      rw [hcur_key]; exact e2ka_encodeKey_pos 1#32 rest₁
    have hrest1_le_cur : rest₁.length ≤ cur.length := Nat.le_of_lt hrest1_lt_cur
    have hgt_lim : ¬ cur.length ≤ limit := by omega
    have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hd : decodeVarint cur = some (0x0a#64, rest₁) := by
      rw [hcur_key]; exact e2ka_decodeVarint_key1 rest₁
    have hrest1_le : rest₁.length ≤ x.bs.length := Nat.le_trans hrest1_le_cur hcur_le
    have hrest1_lt : rest₁.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le hbs_lt
    have hrest1_suf : IsDropSuffix x.bs rest₁ :=
      suffix_trans hcur_le hcur_suf hrest1_le_cur (decodeVarint_suffix hd)
    have hu64 : (V1State.Unchunked.Ct1Sent.encodeRaw u).length < 2 ^ 64 := by
      have hle := e2ka_lenPrefixed_raw_le (V1State.Unchunked.Ct1Sent.encodeRaw u) cur₁
      change (V1State.Unchunked.Ct1Sent.encodeRaw u).length ≤ rest₁.length at hle
      omega
    refine e2ka_b300_decode_key_ok hVarintCall hFitTight
      (SpqrTightEvs.nil maxOps 731332 2560) hgt_lim hsp_align hcur_le hcur_lt hcur_suf
      hd (by decide) (hwt := (by decide : WireType.ofNat? ((0x0a#64 : BitVec 64).toNat % 8) = some .lengthDelimited))
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
    obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have htag1_eq : (0x0a#64 : BitVec 64).toNat / 8 = 1 := by decide
    rw [htag1_eq] at hx1_1
    let rest1Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest₁.length)
    let x_uc : UnchunkedCt1SentMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, rest1Ptr, rest₁⟩
    have hDom_uc : tlb_UcCt1SentDom x_uc := ⟨rfl, rfl, u, cur₁, hValUc u rfl, rfl⟩
    have huc_res :
        (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest₁ 98).toOption = some (u, cur₁) :=
      e2ka_mergeMessage_ucCt1Sent_ok u cur₁ hu64
    apply sepWPpLscro_of_vm (mid := lsmpl.base 312)
    by_vm_steps
      (conv => arg 4; rw [e2ka_b300TightPre, chunkedCt1SampledPBCapAt,
        show (default : V1State.Chunked.Ct1Sampled).uc = none from rfl,
        optUnchunkedCt1SentPBCapAt, memRegion_ct1Sent_none_split x.msgPtr,
        sliceCursorAfter_eq_split hrest1_le hrest1_suf, chunkedBelow_eq_unchunked s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w120; apply SepWP.exists_elim; intro w72
      apply SepWP.exists_elim; intro w64; apply SepWP.exists_elim; intro w56
      apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (e2ka_default_ct1Sent_entails_zeroCap A.repAlloc x.msgPtr) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_uc, M.stepEvents [] st))
        (ret_pc := entry + 416#64) hUcTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_ucCt1SentMergeTightSpecOfEnv, x_uc]
              rw [tlb_domHeap_of_dom hDom_uc]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hrest1_lt,
          tlb_fitsEnv_guarded_of_dom hDom_uc
            (e2ka_fitsEnv_step_suffix hFitTight fun evs h => by
              rw [List.nil_append]
              simpa only [List.append_nil] using
                e2ka_b300_tightEnv_combine hOps h
                  (SpqrTightEvs.nil encOps 342615 2560)
                  (SpqrTightEvs.nil decOps 342615 2560))⟩)
        (by dsimp only [rest1Ptr]; sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m,
              hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m
           hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_ucCt1SentMergeTightSpecOfEnv,
          unchunkedCt1SentMergeSpecOfEnv, UnchunkedCt1SentMergePostEnv, x_uc, huc_res, hsp1,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_u
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_u
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest1_le hrest1_suf hcur1_le_rest1) (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        have hevs_u_tight : tlb_UcCt1SentTightEnvOf ucOps evs_u :=
          tlb_guardedEnv_tight_of_dom hDom_uc hevs_u
        have hst_eq : M.stepEvents evs_u (M.stepEvents [] st) = M.stepEvents evs_u st := rfl
        rw [hst_eq, ← A.pool_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2ka_b300TightPre A lim st evs_u s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { (default : V1State.Chunked.Ct1Sampled) with uc := some u } x.bs cur₁)
          (by
            dsimp only [e2ka_b300TightPre, chunkedCt1SampledPBCapAt, optUnchunkedCt1SentPBCapAt]
            rw [chunkedBelow_eq_unchunked]
            sep_entail)
        have hcur1_le : cur₁.length ≤ x.bs.length := Nat.le_trans hcur1_le_rest1 hrest1_le
        have hcur1_suf : IsDropSuffix x.bs cur₁ :=
          suffix_trans hrest1_le hrest1_suf hcur1_le_rest1 (proto_mergeMessage_suffix huc_res).2
        exact hcont evs_u _ hevs_u_tight hcur1_le hcur1_suf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

/-- Field 2 (`sendingCt1 : Option PolynomialEncoder`, Tag `2`, with `sendingCt1 = none`):
advances `cur₁ = Proto.encodeOptMessage PolynomialEncoder.encodeRaw 2#32 pbEnc ++ cur₂` to `cur₂`
with `evsEnc` satisfying `tlb_PolyEncoderTightEnvOf encOps evsEnc`. -/
theorem e2ka_b300_opt2_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyEncTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps))))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {evsUc : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {pbUc : Option V1State.Unchunked.Ct1Sent}
    {pbEnc : Option PolynomialEncoder} {cur₁ cur₂ : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (tlb_ChunkedCt1SampledTightEnvOf maxOps))
    (hUcEvs : tlb_UcCt1SentTightEnvOf ucOps evsUc)
    (hValEnc : ∀ pe, pbEnc = some pe → tlb_ValidPolyEncoderPB pe)
    (hcur1_eq : cur₁ = encodeOptMessage PolynomialEncoder.encodeRaw 2#32 pbEnc ++ cur₂)
    (hlim_le_cur2 : limit ≤ cur₂.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hcur1_le : cur₁.length ≤ x.bs.length) (hcur1_suf : IsDropSuffix x.bs cur₁)
    (hcont : ∀ (evsEnc : List AllocEvent) (s' : State),
      tlb_PolyEncoderTightEnvOf encOps evsEnc →
      cur₂.length ≤ x.bs.length → IsDropSuffix x.bs cur₂ →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (e2ka_b300TightPre A lim st (evsUc ++ evsEnc) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc, sendingCt1 := pbEnc } x.bs cur₂)
        (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (e2ka_b300TightPre A lim st evsUc s0 s x.msgPtr x.bufRef x.slot x.ptr
        { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc } x.bs cur₁)
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases pbEnc with _ | pe
  · have hcur2 : cur₁ = cur₂ := by simpa [encodeOptMessage] using hcur1_eq
    subst hcur2
    have hevs_eq : evsUc ++ ([] : List AllocEvent) = evsUc := List.append_nil evsUc
    have hm_eq :
        ({ (default : V1State.Chunked.Ct1Sampled) with uc := pbUc, sendingCt1 := none } :
          V1State.Chunked.Ct1Sampled) =
        { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc } := rfl
    refine SepWPpLscro.weaken_pre (P' := e2ka_b300TightPre A lim st (evsUc ++ []) s0 s
        x.msgPtr x.bufRef x.slot x.ptr
        { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc, sendingCt1 := none } x.bs cur₁)
      (by rw [hevs_eq, hm_eq]; exact Entails.refl _) ?_
    exact hcont [] s (SpqrTightEvs.nil encOps 342615 2560) hcur1_le hcur1_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
  · let rest₂ := tlb_lenPrefixed (PolynomialEncoder.encodeRaw pe) cur₂
    have hcur1_key : cur₁ = encodeKey 2#32 .lengthDelimited ++ rest₂ := by
      rw [hcur1_eq]
      exact e2ka_encodeOptMessage_some_append PolynomialEncoder.encodeRaw 2#32 pe cur₂
    have hcur2_le_rest2 : cur₂.length ≤ rest₂.length := e2ka_lenPrefixed_ge_tail _ _
    have hrest2_lt_cur1 : rest₂.length < cur₁.length := by
      rw [hcur1_key]; exact e2ka_encodeKey_pos 2#32 rest₂
    have hrest2_le_cur1 : rest₂.length ≤ cur₁.length := Nat.le_of_lt hrest2_lt_cur1
    have hgt_lim : ¬ cur₁.length ≤ limit := by omega
    have hcur1_lt : cur₁.length < 2 ^ 63 := by omega
    have hd : decodeVarint cur₁ = some (0x12#64, rest₂) := by
      rw [hcur1_key]; exact e2ka_decodeVarint_key2 rest₂
    have hrest2_le : rest₂.length ≤ x.bs.length := Nat.le_trans hrest2_le_cur1 hcur1_le
    have hrest2_suf : IsDropSuffix x.bs rest₂ :=
      suffix_trans hcur1_le hcur1_suf hrest2_le_cur1 (decodeVarint_suffix hd)
    have hpe64 : (PolynomialEncoder.encodeRaw pe).length < 2 ^ 64 := by
      have hle := e2ka_lenPrefixed_raw_le (PolynomialEncoder.encodeRaw pe) cur₂
      change (PolynomialEncoder.encodeRaw pe).length ≤ rest₂.length at hle
      omega
    have hAcc1 : tlb_ChunkedCt1SampledTightEnvOf maxOps evsUc := by
      simpa using e2ka_b300_tightEnv_combine hOps hUcEvs
        (SpqrTightEvs.nil encOps 342615 2560) (SpqrTightEvs.nil decOps 342615 2560)
    refine e2ka_b300_decode_key_ok hVarintCall hFitTight hAcc1 hgt_lim hsp_align
      hcur1_le hcur1_lt hcur1_suf hd (by decide)
      (hwt := (by decide : WireType.ofNat? ((0x12#64 : BitVec 64).toNat % 8) = some .lengthDelimited))
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
    obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have htag2_eq : (0x12#64 : BitVec 64).toNat / 8 = 2 := by decide
    rw [htag2_eq] at hx1_1
    have hb1_1 : (BitVec.ofNat 32 2 == 1#32) = false := by decide
    have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 2) == 1#32) = false := by decide
    let rest2Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest₂.length)
    let x_pe : PolyEncoderMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 128#64, default, x.bufRef, x.slot, rest2Ptr, rest₂⟩
    have hDom_pe : tlb_PolyEncoderDom x_pe := ⟨rfl, rfl, pe, cur₂, hValEnc pe rfl, rfl⟩
    have hpe_res :
        (mergeMessage PolynomialEncoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest₂ 98).toOption = some (pe, cur₂) :=
      e2ka_mergeMessage_polyEncoder_ok pe cur₂ hpe64
    apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
    by_vm_steps
      (conv => arg 4; dsimp only [e2ka_b300TightPre, chunkedCt1SampledPBCapAt, optPolynomialEncoderPBAt])
      (conv => arg 4; rw [show (default : V1State.Chunked.Ct1Sampled).sendingCt1 = none from rfl,
        memRegion_polyEncoder_none_split (x.msgPtr + 128#64),
        sliceCursorAfter_eq_split hrest2_le hrest2_suf, chunkedBelow_eq_poly s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w48; apply SepWP.exists_elim; intro w40
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (e2ka_default_polyEncoder_entails_zeroCap A.repAlloc (x.msgPtr + 128#64))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_pe, M.stepEvents evsUc st))
        (ret_pc := entry + 356#64) hPolyEncTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_polyEncoderMergeTightSpecOfEnv, x_pe]
              rw [tlb_domHeap_of_dom hDom_pe]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          by change ([] : List (List (BitVec 8))).length + rest₂.length < 2 ^ 56;
             simp only [List.length_nil, Nat.zero_add]; omega,
          by change ([] : List (List (BitVec 8))).length + rest₂.length < 2 ^ 56;
             simp only [List.length_nil, Nat.zero_add]; omega,
          tlb_fitsEnv_guarded_of_dom hDom_pe
            (e2ka_fitsEnv_step_suffix hFitTight fun evs h => by
              simpa using e2ka_b300_tightEnv_combine hOps hUcEvs h
                (SpqrTightEvs.nil decOps 342615 2560))⟩)
        (by dsimp only [rest2Ptr]; sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m,
              hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m
           hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv,
          polyEncoderMergeSpecOfEnv, x_pe, hpe_res, hsp1, protoPolynomialEncoderAt_eq_pb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest2_le hrest2_suf hcur2_le_rest2) (by sep_focus)
        apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A.repAlloc x.msgPtr pbUc hcur2_le_rest2)
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        have hevs_p_tight : tlb_PolyEncoderTightEnvOf encOps evs_p :=
          tlb_guardedEnv_tight_of_dom hDom_pe hevs_p
        rw [← e2ka_stepEvents_append evsUc evs_p st, ← A.pool_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2ka_b300TightPre A lim st (evsUc ++ evs_p) s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc, sendingCt1 := some pe }
            x.bs cur₂)
          (by
            dsimp only [e2ka_b300TightPre, chunkedCt1SampledPBCapAt, optPolynomialEncoderPBAt]
            rw [chunkedBelow_eq_poly]
            sep_entail)
        have hcur2_le : cur₂.length ≤ x.bs.length := Nat.le_trans hcur2_le_rest2 hrest2_le
        have hcur2_suf : IsDropSuffix x.bs cur₂ :=
          suffix_trans hrest2_le hrest2_suf hcur2_le_rest2 (proto_mergeMessage_suffix hpe_res).2
        exact hcont evs_p _ hevs_p_tight hcur2_le hcur2_suf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

/-- Field 3 (`receivingEk : Option PolynomialDecoder`, Tag `3`, with `receivingEk = none`):
advances `cur₂ = Proto.encodeOptMessage PolynomialDecoder.encodeRaw 3#32 pbDec ++ tail` to `tail`
with `evsDec` satisfying `tlb_PolyDecoderTightEnvOf decOps evsDec`. -/
theorem e2ka_b300_opt3_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ucOps encOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : ucOps + encOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyDecTightCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps))))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {evsUc evsEnc : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {pb : V1State.Chunked.Ct1Sampled} {cur₂ tail : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (tlb_ChunkedCt1SampledTightEnvOf maxOps))
    (hUcEvs : tlb_UcCt1SentTightEnvOf ucOps evsUc)
    (hEncEvs : tlb_PolyEncoderTightEnvOf encOps evsEnc)
    (hValDec : ∀ pd, pb.receivingEk = some pd → tlb_ValidPolyDecoderPB pd)
    (hcur2_eq : cur₂ = encodeOptMessage PolynomialDecoder.encodeRaw 3#32 pb.receivingEk ++ tail)
    (hlim_eq_tail : tail.length = limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hcur2_le : cur₂.length ≤ x.bs.length) (hcur2_suf : IsDropSuffix x.bs cur₂)
    (hcont : ∀ (evsDec : List AllocEvent) (s' : State),
      tlb_PolyDecoderTightEnvOf decOps evsDec →
      tail.length ≤ x.bs.length → IsDropSuffix x.bs tail →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (e2ka_b300TightPre A lim st (evsUc ++ evsEnc ++ evsDec) s0 s' x.msgPtr x.bufRef x.slot
          x.ptr pb x.bs tail)
        (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (e2ka_b300TightPre A lim st (evsUc ++ evsEnc) s0 s x.msgPtr x.bufRef x.slot x.ptr
        { (default : V1State.Chunked.Ct1Sampled) with uc := pb.uc, sendingCt1 := pb.sendingCt1 }
        x.bs cur₂)
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  rcases pb with ⟨pbUc, pbEnc, pbDec⟩
  dsimp only at hValDec hcur2_eq ⊢
  rcases pbDec with _ | pd
  · have htail : cur₂ = tail := by simpa [encodeOptMessage] using hcur2_eq
    subst htail
    have hevs_eq : (evsUc ++ evsEnc) ++ ([] : List AllocEvent) = evsUc ++ evsEnc :=
      List.append_nil _
    have hm_eq :
        (⟨pbUc, pbEnc, none⟩ : V1State.Chunked.Ct1Sampled) =
        { (default : V1State.Chunked.Ct1Sampled) with uc := pbUc, sendingCt1 := pbEnc } := rfl
    refine SepWPpLscro.weaken_pre
      (P' := e2ka_b300TightPre A lim st (evsUc ++ evsEnc ++ []) s0 s x.msgPtr x.bufRef x.slot
        x.ptr ⟨pbUc, pbEnc, none⟩ x.bs cur₂)
      (by rw [hevs_eq, hm_eq]; exact Entails.refl _) ?_
    exact hcont [] s (SpqrTightEvs.nil decOps 342615 2560) hcur2_le hcur2_suf
      hpc hrun hsp htr hx21 hx22 hcs
  · let rest₃ := tlb_lenPrefixed (PolynomialDecoder.encodeRaw pd) tail
    have hcur2_key : cur₂ = encodeKey 3#32 .lengthDelimited ++ rest₃ := by
      rw [hcur2_eq]
      exact e2ka_encodeOptMessage_some_append PolynomialDecoder.encodeRaw 3#32 pd tail
    have htail_le_rest3 : tail.length ≤ rest₃.length := e2ka_lenPrefixed_ge_tail _ _
    have hrest3_lt_cur2 : rest₃.length < cur₂.length := by
      rw [hcur2_key]; exact e2ka_encodeKey_pos 3#32 rest₃
    have hrest3_le_cur2 : rest₃.length ≤ cur₂.length := Nat.le_of_lt hrest3_lt_cur2
    have hgt_lim : ¬ cur₂.length ≤ limit := by omega
    have hcur2_lt : cur₂.length < 2 ^ 63 := by omega
    have hd : decodeVarint cur₂ = some (0x1a#64, rest₃) := by
      rw [hcur2_key]; exact e2ka_decodeVarint_key3 rest₃
    have hrest3_le : rest₃.length ≤ x.bs.length := Nat.le_trans hrest3_le_cur2 hcur2_le
    have hrest3_suf : IsDropSuffix x.bs rest₃ :=
      suffix_trans hcur2_le hcur2_suf hrest3_le_cur2 (decodeVarint_suffix hd)
    have hpd64 : (PolynomialDecoder.encodeRaw pd).length < 2 ^ 64 := by
      have hle := e2ka_lenPrefixed_raw_le (PolynomialDecoder.encodeRaw pd) tail
      change (PolynomialDecoder.encodeRaw pd).length ≤ rest₃.length at hle
      omega
    have hAcc2 : tlb_ChunkedCt1SampledTightEnvOf maxOps (evsUc ++ evsEnc) := by
      simpa using e2ka_b300_tightEnv_combine hOps hUcEvs hEncEvs
        (SpqrTightEvs.nil decOps 342615 2560)
    refine e2ka_b300_decode_key_ok hVarintCall hFitTight hAcc2 hgt_lim hsp_align
      hcur2_le hcur2_lt hcur2_suf hd (by decide)
      (hwt := (by decide : WireType.ofNat? ((0x1a#64 : BitVec 64).toNat % 8) = some .lengthDelimited))
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
    obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have htag3_eq : (0x1a#64 : BitVec 64).toNat / 8 = 3 := by decide
    rw [htag3_eq] at hx1_1
    have hb1_1 : (BitVec.ofNat 32 3 == 1#32) = false := by decide
    have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 3) == 1#32) = false := by decide
    have hb2_1 : (BitVec.ofNat 32 3 == 2#32) = false := by decide
    have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 3) == 2#32) = false := by decide
    let rest3Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest₃.length)
    let x_pd : PolyDecoderMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 184#64, default, x.bufRef, x.slot, rest3Ptr, rest₃⟩
    have hDom_pd : tlb_PolyDecoderDom x_pd := ⟨rfl, rfl, pd, tail, hValDec pd rfl, rfl⟩
    have hpd_res :
        (mergeMessage PolynomialDecoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest₃ 98).toOption = some (pd, tail) :=
      e2ka_mergeMessage_polyDecoder_ok pd tail hpd64
    apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
    by_vm_steps
      (conv => arg 4; dsimp only [e2ka_b300TightPre, chunkedCt1SampledPBCapAt, optPolynomialDecoderPBAt])
      (conv => arg 4; rw [show (default : V1State.Chunked.Ct1Sampled).receivingEk = none from rfl,
        memRegion_polyDecoder_none_split (x.msgPtr + 184#64),
        sliceCursorAfter_eq_split hrest3_le hrest3_suf, chunkedBelow_eq_poly s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (e2ka_default_polyDecoder_entails_zeroCap A.repAlloc (x.msgPtr + 184#64))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_pd, M.stepEvents (evsUc ++ evsEnc) st))
        (ret_pc := entry + 304#64) hPolyDecTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_polyDecoderMergeTightSpecOfEnv, x_pd]
              rw [tlb_domHeap_of_dom hDom_pd]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          by change ([] : List (List (BitVec 8))).length + rest₃.length < 2 ^ 56;
             simp only [List.length_nil, Nat.zero_add]; omega,
          tlb_fitsEnv_guarded_of_dom hDom_pd
            (e2ka_fitsEnv_step_suffix hFitTight fun evs h =>
              e2ka_b300_tightEnv_combine hOps hUcEvs hEncEvs h)⟩)
        (by dsimp only [rest3Ptr]; sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m,
              hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m
           hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv,
          polyDecoderMergeSpecOfEnv, x_pd, hpd_res, hsp1, protoPolynomialDecoderAt_eq_pb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_d
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_d
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest3_le hrest3_suf htail_le_rest3) (by sep_focus)
        apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A.repAlloc x.msgPtr pbUc htail_le_rest3)
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        have hevs_d_tight : tlb_PolyDecoderTightEnvOf decOps evs_d :=
          tlb_guardedEnv_tight_of_dom hDom_pd hevs_d
        rw [← e2ka_stepEvents_append (evsUc ++ evsEnc) evs_d st, ← A.pool_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2ka_b300TightPre A lim st (evsUc ++ evsEnc ++ evs_d) s0 _ x.msgPtr x.bufRef
            x.slot x.ptr ⟨pbUc, pbEnc, some pd⟩ x.bs tail)
          (by
            dsimp only [e2ka_b300TightPre, chunkedCt1SampledPBCapAt, optPolynomialDecoderPBAt]
            rw [chunkedBelow_eq_poly]
            sep_entail)
        have htail_le : tail.length ≤ x.bs.length := Nat.le_trans htail_le_rest3 hrest3_le
        have htail_suf : IsDropSuffix x.bs tail :=
          suffix_trans hrest3_le hrest3_suf htail_le_rest3 (proto_mergeMessage_suffix hpd_res).2
        exact hcont evs_d _ hevs_d_tight htail_le htail_suf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

private theorem e2ka_b300_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {maxOps : Nat}
    (x : ChunkedCt1SampledMergeGhost)
    (s0 s sf : State) (pb : V1State.Chunked.Ct1Sampled) (tail : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedCt1SampledDom x)
    (hsome : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : tlb_ChunkedCt1SampledTightEnvOf maxOps evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
          ((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs tail))) ⊢
    (e2ka_b300TightSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2ka_b300TightSpec, chunkedCt1SampledMergeSpecOfEnv,
    ChunkedCt1SampledMergePostEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
          ((x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs tail))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedCt1SampledPBCapAt A.repAlloc x.msgPtr tail.length pb ∗
            sliceCursorAfter x.slot x.ptr x.bs tail))))) ?_
  refine sepConj_mono_right (sepConj_mono ?_
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))
  rw [← A.pool_of_vmPreserved hvm]
  exact Entails.trans (Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _))
    (Entails.sepExists_right evs (Entails.refl _))

/-- Canonical `Ok` epilogue at `entry + 192#64` when `tail.length = limit`. -/
theorem e2ka_b300_ret_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {pb : V1State.Chunked.Ct1Sampled} {tail : List (BitVec 8)} {limit : Nat}
    (hDom : tlb_ChunkedCt1SampledDom x)
    (hevs : tlb_ChunkedCt1SampledTightEnvOf maxOps evs)
    (heq_lim : tail.length = limit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsome : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, tail))
    (htail_le : tail.length ≤ x.bs.length) (htail_suf : IsDropSuffix x.bs tail)
    (hpc : s.pc = (blkPl_300).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (e2ka_b300TightPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr pb x.bs tail)
      (WppPost (e2ka_b300TightSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  let tailPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - tail.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; rw [e2ka_b300TightPre, chunkedSavedRegs,
      sliceCursorAfter_eq_split htail_le htail_suf, sliceCursorAt])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      arm64_norm, hsp])
    wp_steps
    apply SepWP.fold (stackAt_chunkedMerge_epilogue s0) (by unfold chunkedSavedRegs; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ tailPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - tail.length)) ∗ (tailPtr ↦ₛ tail) ⊢
        sliceCursorAfter x.slot x.ptr x.bs tail := by
      rw [sliceCursorAfter_eq_split htail_le htail_suf, sliceCursorAt]
      dsimp only [tailPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [tailPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx26, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2ka_b300_ok_exit_entails A lim st x s0 s _ pb tail evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

end Steps

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB300StepsPlacedBudget
