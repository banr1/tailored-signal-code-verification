/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudgetSteps
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledUcBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommon
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.Ct2Sampled::merge` (Block `301`)

Proves `tlb_ChunkedCt2SampledMergePlacedTightOkOf` on Block `301` within
`SpqrTightEvs maxOps 345567 2560` (`authOps + encOps ≤ maxOps`, default `39 = 4 + 35`: inlined
`Unchunked.Ct2Sampled` `Authenticator` `2,952` B + `PolynomialEncoder` `342,615` B) on canonical
`tlb_ChunkedCt2SampledDom` inputs, falling back to `ChunkedCt2SampledMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB301PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   libsignalSessionLib ls_blockPlacement_base lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_encodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_lt key_wt_some pointsToBytes_prefix_join sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false
   ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authenticatorPBCapAt memRegion_40_cells optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono protoEncodeVarint_eq_codec setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderAt protoPolynomialEncoderPinnedAt vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr
  (noneCap2 optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt2SampledMergeGhost ChunkedInl10CalleeSaved OptPolyEncoderBound PolyEncoderMergeGhost
   SepWPpLscro bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedCt2SampledMerge_fnOff chunkedCt2SampledPBCapAt chunkedCt2SampledPBCapAt_mono
   chunkedInlBelowStack chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_eq_polyMerge chunkedInlSavedRegs10 chunkedInlStack
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   default_unchunked2_entails_cap memRegion_48_split_40_8 memRegion_polyEncoder_none_split_inl
   optCt2SentPBCapAt optCt2SentPBCapAt_mono optPolynomialEncoderPBAt_some_eq polyEncoderToProto
   proto_mergeMessage_suffix setWidth8_zext64_trunc32_ofNat64_wt_ct2
   stackAt_chunkedInl10_epilogue stackAt_chunkedInl_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp unchunked2CapAt unchunked2CapAt_mono
   vecU8At_eq_header_sep_buf vecU8Buf withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_301 blkPl_301)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedCt2SampledDom tlb_ChunkedCt2SampledGuardedEnvOf
   tlb_ChunkedCt2SampledMergePlacedTightOk tlb_ChunkedCt2SampledMergePlacedTightOkOf
   tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf tlb_PolyEncoderMergePlacedTightOkOf
   tlb_ValidAuthPB tlb_ValidChunkedCt2SampledPB tlb_ValidOptAuthPB tlb_ValidPolyEncoderPB
   tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt tlb_domHeap_of_dom
   tlb_fitsEnv_fallback_of_not_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed
   tlb_polyEncoderMergeTightSpecOfEnv tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergePostEnv authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2SampledBudget
  (chunked_ct2_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedCt2SampledMergeEnv chunkedCt2SampledMergePostEnv_imp_pre
   chunkedCt2SampledMergeSpec chunkedCt2SampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergePostEnv polyEncoderMergeSpec polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem e2b301_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2b301_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2b301_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2b301_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2b301_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2b301_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2b301_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2b301_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2b301_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt2SampledMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2b301_sp_setMem_pre e2b301_pc_setMem_pre e2b301_status_setMem_pre e2b301_pstate_setMem_pre
  e2b301_trace_setMem_pre e2b301_readReg64_setMem_pre e2b301_readReg32_setMem_pre
  e2b301_readReg_setMem_pre e2b301_calleeSavedVRegs_setMem_pre

private theorem e2b301_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ## 1. Cross-Block & `withLsCodeLoaded → withLsCodeRoLoaded` Transfer Helpers -/

private theorem e2b301_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
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

private theorem e2b301_subroutine_ok_cro_of_cl [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded h

/-! ## 2. Zero-Capacity Initialization Fold Lemmas (`cap = 0#64` for Blocks `295` and `297`) -/

private theorem e2b301_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b301_default_auth_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) []
  have h1 := e2b301_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b301_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

private theorem e2b301_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b301_default_polyEncoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + 24#64) [] ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := e2b301_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h2 := e2b301_pointsTo_zero_entails_vecVecU8ZeroPin A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

/-! ## 3. Pure Codec Round-Trip & Wire-Splitting Lemmas on `tlb_ChunkedCt2SampledDom` -/

private theorem e2b301_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> cases h
  rfl

private theorem e2b301_lenPrefixed_decodeVarint (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) = some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc, protoEncodeVarint_eq_codec]
  exact decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)

private theorem e2b301_lenPrefixed_length_gt (raw rest : List (BitVec 8)) :
    raw.length + rest.length < (tlb_lenPrefixed raw rest).length := by
  simpa only [List.length_append] using
    decodeVarint_length (e2b301_lenPrefixed_decodeVarint raw rest)

private theorem e2b301_mergeMessage_ch_ct2Sampled (pb : V1State.Chunked.Ct2Sampled)
    (rest : List (BitVec 8))
    (hraw : (V1State.Chunked.Ct2Sampled.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.Ct2Sampled.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.Ct2Sampled.encodeRaw pb) rest) 99).toOption =
      some (pb, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Chunked.Ct2Sampled.mergeField 2 V1State.Chunked.Ct2Sampled.encodeRaw
    default pb 99 rest
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_ch_ct2Sampled pb hraw) hraw (by decide)]
  rfl

private theorem e2b301_mergeMessage_auth (auth : ProtoAuthenticator)
    (after : List (BitVec 8))
    (hraw : (ProtoAuthenticator.encodeRaw auth).length < 2 ^ 64) :
    (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw auth) after) 97).toOption =
      some (auth, after) := by
  change (mergeMessage ProtoAuthenticator.mergeField .lengthDelimited
    default (tlb_lenPrefixed (ProtoAuthenticator.encodeRaw auth) after) 97).toOption =
    some (auth, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw
    default auth 97 after
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_authenticator auth hraw) hraw (by decide)]
  rfl

private theorem e2b301_mergeMessage_polyEncoder (e : PolynomialEncoder)
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

private theorem e2b301_encodeOptMessage_uc_tag1_some (u : V1State.Unchunked.Ct2Sent)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.Ct2Sent.encodeRaw 1#32 (some u) ++ after =
      0x0a#8 :: tlb_lenPrefixed (V1State.Unchunked.Ct2Sent.encodeRaw u) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited =
      [0x0a#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b301_encodeOptMessage_auth_tag2_some (auth : ProtoAuthenticator)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 (some auth) ++ after =
      0x12#8 :: tlb_lenPrefixed (ProtoAuthenticator.encodeRaw auth) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited =
      [0x12#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b301_encodeOptMessage_poly_tag2_some (e : PolynomialEncoder)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 (some e) ++ after =
      0x12#8 :: tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited =
      [0x12#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b301_decodeVarint_0x08 (r : List (BitVec 8)) :
    decodeVarint (0x08#8 :: r) = some (0x08#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x08#64 = [0x08#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x08#64 r

private theorem e2b301_decodeVarint_0x0a (r : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: r) = some (0x0a#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x0a#64 = [0x0a#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x0a#64 r

private theorem e2b301_decodeVarint_0x12 (r : List (BitVec 8)) :
    decodeVarint (0x12#8 :: r) = some (0x12#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x12#64 = [0x12#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x12#64 r

private theorem e2b301_decodeVarint_protoVarint (v : BitVec 64) (after : List (BitVec 8)) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ after) =
      some (v, after) := by
  rw [protoEncodeVarint_eq_codec]
  exact decodeVarint_encodeVarint v after

private theorem e2b301_ct2Sent_encodeRaw_split (u : V1State.Unchunked.Ct2Sent)
    (after : List (BitVec 8)) :
    V1State.Unchunked.Ct2Sent.encodeRaw u ++ after =
      (if u.epoch == 0#64 then []
       else 0x08#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch) ++
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ProtoAuthenticator.encodeRaw 2#32 u.auth ++ after) := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := by
    decide
  unfold V1State.Unchunked.Ct2Sent.encodeRaw
  dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field]
  split <;> simp only [hkey, List.cons_append, List.nil_append, List.append_assoc]

/-! ## 4. Model-Generic `stepEvents` & `FitsEnv` Discharges -/

private theorem e2b301_stepEvents_nil {M : AllocCostModel} (st : M.σ) :
    M.stepEvents [] st = st := rfl

private theorem e2b301_stepEvents_append {M : AllocCostModel} (st : M.σ)
    (evs₁ evs₂ : List AllocEvent) :
    M.stepEvents evs₂ (M.stepEvents evs₁ st) = M.stepEvents (evs₁ ++ evs₂) st := by
  unfold AllocCostModel.stepEvents
  rw [List.foldl_append]

private theorem e2b301_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs h
  rw [decodeVarint2Env_eq_nil_of_some hd h]
  trivial

private theorem e2b301_fitsEnv_auth_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps maxOps : Nat} {evs : List AllocEvent} {x_auth : AuthMergeGhost}
    (hOps : authOps ≤ maxOps)
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hDom_auth : tlb_AuthDom x_auth)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560)) :
    FitsEnv M lim (M.stepEvents evs st) (tlb_AuthGuardedEnvOf authOps x_auth) := by
  intro evs_a h_a
  have htight_a : SpqrTightEvs authOps 2952 32 evs_a :=
    tlb_guardedEnv_tight_of_dom hDom_auth h_a
  have hcomb : SpqrTightEvs maxOps 345567 2560 (evs ++ evs_a) :=
    SpqrTightEvs.mono (by omega) (by decide) (by decide) (hevs.append htight_a)
  exact ((fitsEvents_append M lim evs evs_a st).mp (hFit (evs ++ evs_a) hcomb)).2

private theorem e2b301_fitsEnv_poly_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {o₁ c₁ r₁ encOps maxOps : Nat} {evs : List AllocEvent} {x_poly : PolyEncoderMergeGhost}
    (hOps : o₁ + encOps ≤ maxOps)
    (hCum : c₁ + 342615 ≤ 345567)
    (hReq : max r₁ 2560 ≤ 2560)
    (hevs : SpqrTightEvs o₁ c₁ r₁ evs)
    (hDom_poly : tlb_PolyEncoderDom x_poly)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560)) :
    FitsEnv M lim (M.stepEvents evs st) (tlb_PolyEncoderGuardedEnvOf encOps x_poly) := by
  intro evs_p h_p
  have htight_p : SpqrTightEvs encOps 342615 2560 evs_p :=
    tlb_guardedEnv_tight_of_dom hDom_poly h_p
  have hcomb : SpqrTightEvs maxOps 345567 2560 (evs ++ evs_p) :=
    SpqrTightEvs.mono hOps hCum hReq (hevs.append htight_p)
  exact ((fitsEvents_append M lim evs evs_p st).mp (hFit (evs ++ evs_p) hcomb)).2


/-! ## 5. Straight-Line `SepWPpLscro` Step Lemmas on `tlb_ChunkedCt2SampledDom` -/

private def e2b301_domLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State.Chunked.Ct2Sampled)
    (bs cur : List (BitVec 8)) : SepProp :=
  chunkedCt2SampledPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
    memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool lim (M.stepEvents evs st) s

private def e2b301_domUcLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (hdr : Option PolynomialEncoder)
    (uc : V1State.Unchunked.Ct2Sent) (bs cur : List (BitVec 8)) : SepProp :=
  optPolynomialEncoderPBAt A.repAlloc msgPtr hdr ∗
    unchunked2CapAt A.repAlloc (msgPtr + 0x38#64) cur.length uc.epoch uc.auth ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
    memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗
    (bufRef ↦₆₄ slot) ∗
    sliceCursorAfter slot ptr bs cur ∗
    A.pool lim (M.stepEvents evs st) s

private theorem e2b301_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {maxOps : Nat}
    (x : ChunkedCt2SampledMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.Ct2Sampled) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedCt2SampledDom x)
    (hsome : (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 345567 2560 evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (chunkedCt2SampledMergeSpecOfEnv A lim
      (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
      (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)).post (x, st) s0 sf := by
  dsimp only [chunkedCt2SampledMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_right evs
      (Entails.pure_right (Or.inl ⟨hDom, hevs⟩)
        (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)))
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

section Placed

set_option quotPrecheck false in
local notation "entry" => (blkPl_301).base

private theorem e2b301_dom_ok_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    {evs : List AllocEvent}
    (hDom : tlb_ChunkedCt2SampledDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (heq_lim : cur.length = outerLimit)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hevs : SpqrTightEvs maxOps 345567 2560 evs)
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b301_domLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlSavedRegs10,
      sepConj_assoc, arm64_norm, hsp])
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0)
      (by unfold chunkedInlSavedRegs10; sep_focus)
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
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2b301_ok_exit_entails A lim st x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b301_dom_prologue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0_wt : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (hx1_msg : s0.readReg64 .x1 = x.msgPtr)
    (hx2_buf : s0.readReg64 .x2 = x.bufRef)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hwt_ld : x.wt = .lengthDelimited)
    (hdv0 : decodeVarint x.bs = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s : State,
      s.pc = entry + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot →
      s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 24#5) = 1#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
        (e2b301_domLoopPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s0
      (chunkedCt2SampledPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
        ((x.bufRef ↦₆₄ x.slot) ∗ (sliceCursorAt x.slot x.ptr x.bs ∗
          (A.pool lim st s0 ∗ stackAt s0.sp chunkedInlStack))))
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
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
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1
    apply SepWP.exists_elim; intro v2; apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7
    apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9
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
            simp only [A.pool_of_vmPreserved hvm1, e2b301_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf],
        hbs_lt,
        e2b301_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
      at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt hbs_lt)
    have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hsub := bv_len_sub_limit hge_len
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b301_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hevs_nil
      (conv => arg 4; rw [e2b301_stepEvents_nil])
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedCt2SampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domLoopPre A lim st [] s0 _ x.msgPtr x.bufRef x.slot x.ptr
          x.msg x.bs rest0)
        (by dsimp only [e2b301_domLoopPre, sliceCursorAfter]; rw [e2b301_stepEvents_nil];
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
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b301_dom_outer_decode_key [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {iwt : WireType} {outerLimit : Nat} {evs : List AllocEvent}
    (hgt_lim : ¬ cur.length ≤ outerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag_ge1 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = entry + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b301_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 188#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1,
            e2b301_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (e2b301_fitsEnv_decodeVarint2_of_some hd))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    have hshr := key_shr32_of_lt hk_lt
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt htag_ge1
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := entry + 228#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b301_stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hd hevs_dv
      subst hevs_nil
      (conv => arg 4; rw [e2b301_stepEvents_nil])
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedCt2SampledPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2b301_domLoopPre]; sep_entail)
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
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩


private theorem e2b301_dom_uc_decode_key [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType}
    {outerLimit innerLimit : Nat} {evs : List AllocEvent}
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (htag_ge1 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = entry + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b301_domUcLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domUcLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domUcLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 432#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1,
            e2b301_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (e2b301_fitsEnv_decodeVarint2_of_some hd))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    have hshr := key_shr32_of_lt hk_lt
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt htag_ge1
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
      omega
    apply sepWPpLscro_of_vm (mid := entry + 464#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b301_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      have hevs_nil : evs_v = [] := decodeVarint2Env_eq_nil_of_some hd hevs_v
      subst hevs_nil
      (conv => arg 4; rw [e2b301_stepEvents_nil])
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_mono A.repAlloc (x.msgPtr + 0x38#64) uc.epoch uc.auth hrest_le_cur)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domUcLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
        (by dsimp only [e2b301_domUcLoopPre]; sep_entail)
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
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        (by simp only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b301_dom_uc_epoch_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest rest' : List (BitVec 8)} {v : BitVec 64}
    {outerLimit innerLimit : Nat} {evs : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hdv : decodeVarint rest = some (v, rest'))
    (hcont : ∀ s'' : State,
      s''.pc = entry + 412#64 →
      s''.status = .Running → s''.sp = s0.sp - 128#64 → s''.trace = s0.trace →
      s''.readReg64 (Reg.gpr 19#5) = x.bufRef → s''.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s''.readReg64 (Reg.gpr 21#5) = x.slot →
      s''.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s''.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s''.readReg64 (Reg.gpr 24#5) = 1#64 →
      s''.readReg64 (Reg.gpr 25#5) = 8#64 →
      s''.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s'' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s''
        (e2b301_domUcLoopPre A lim st evs s0 s'' x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with epoch := v } x.bs rest')
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domUcLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domUcLoopPre,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 536#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1,
            e2b301_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hrest_lt (e2b301_fitsEnv_decodeVarint2_of_some hdv))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    apply sepWPpLscro_of_vm (mid := entry + 412#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, unchunked2CapAt,
        e2b301_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      have hevs_nil : evs_v = [] := decodeVarint2Env_eq_nil_of_some hdv hevs_v
      subst hevs_nil
      (conv => arg 4; rw [e2b301_stepEvents_nil])
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x38#64) uc.auth hrest'_le)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domUcLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with epoch := v } x.bs rest')
        (by dsimp only [e2b301_domUcLoopPre, unchunked2CapAt]; simp only [arm64_norm]; sep_entail)
      exact hcont _
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        (by simp only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b301_dom_uc_auth_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps maxOps : Nat}
    (hOps_auth : authOps ≤ maxOps)
    (hAuthTightCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {rest rest' : List (BitVec 8)} {auth' : ProtoAuthenticator}
    {outerLimit innerLimit : Nat} {evs : List AllocEvent}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hauth_none : uc.auth = none)
    (hDom_auth : tlb_AuthDom ⟨.lengthDelimited, x.msgPtr + 0x38#64, default, x.bufRef, x.slot,
      x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩)
    (hauth_res : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 97).toOption = some (auth', rest'))
    (hcont : ∀ (evs' : List AllocEvent) (s'' : State),
      SpqrTightEvs authOps 2952 32 evs' →
      s''.pc = entry + 412#64 →
      s''.status = .Running → s''.sp = s0.sp - 128#64 → s''.trace = s0.trace →
      s''.readReg64 (Reg.gpr 19#5) = x.bufRef → s''.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s''.readReg64 (Reg.gpr 21#5) = x.slot →
      s''.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s''.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s''.readReg64 (Reg.gpr 24#5) = 1#64 →
      s''.readReg64 (Reg.gpr 25#5) = 8#64 →
      s''.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s'' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s''
        (e2b301_domUcLoopPre A lim st evs' s0 s'' x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with auth := some auth' } x.bs rest')
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 (WireType.lengthDelimited).toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domUcLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs rest)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_auth : AuthMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr + 0x38#64, default, x.bufRef, x.slot, restPtr, rest⟩
  apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domUcLoopPre, unchunked2CapAt, hauth_none, optAuthenticatorPBCapAt,
      memRegion_40_cells (x.msgPtr + 0x38#64), sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_authMerge s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2
    apply SepWP.exists_elim; intro w3
    apply SepWP.exists_elim; intro w4
    apply SepWP.exists_elim; intro w5
    wp_steps
    have hdef := e2b301_default_auth_entails_zeroCap A.repAlloc (x.msgPtr + 0x38#64)
    simp only [arm64_norm] at hdef
    apply SepWP.fold hdef (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_auth, M.stepEvents evs st))
      (ret_pc := entry + 516#64) hAuthTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [tlb_authMergeTightSpecOfEnv, x_auth];
          rw [tlb_domHeap_of_dom hDom_auth];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm,
            hsp, hx0, hx20, hx19, setWidth8_ofNat64_wt]; try rfl)
      (And.intro hrest_lt (e2b301_fitsEnv_auth_tight hOps_auth hevs hDom_auth hFitTight))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_res).1
    apply sepWPpLscro_of_vm (mid := entry + 412#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv, AuthMergePostEnv,
        x_auth, hauth_res, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_auth
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
      have htight_a : SpqrTightEvs authOps 2952 32 evs_auth :=
        tlb_guardedEnv_tight_of_dom hDom_auth hevs_auth
      have hevs' : SpqrTightEvs authOps 2952 32 (evs ++ evs_auth) :=
        SpqrTightEvs.mono (by omega) (by decide) (by decide) (hevs.append htight_a)
      (conv => arg 4; rw [e2b301_stepEvents_append])
      apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      let s_end : State := (sm.writeReg64 (Reg.gpr 1#5) 0#64).setPC (entry + 412#64)
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domUcLoopPre A lim st (evs ++ evs_auth) s0 s_end x.msgPtr x.bufRef x.slot x.ptr
          hdr { uc with auth := some auth' } x.bs rest')
        (by dsimp only [e2b301_domUcLoopPre, unchunked2CapAt, optAuthenticatorPBCapAt, s_end];
            simp only [arm64_norm]; sep_entail)
      exact hcont (evs ++ evs_auth) s_end hevs'
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hrunm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hspm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, htrm, htr])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx19_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx20_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx21_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx22_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx23_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx24_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx25_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx26_m])
        ⟨by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx27_m],
         by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx28_m],
         by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b301_dom_uc_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {hdr : Option PolynomialEncoder} {uc : V1State.Unchunked.Ct2Sent}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat} {evs : List AllocEvent}
    (heq_lim : cur.length = innerLimit)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ s' : State,
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b301_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { sendingCt2 := hdr, uc := some uc } x.bs cur)
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 412#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domUcLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr hdr uc x.bs cur)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_vm (mid := entry + 168#64)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    rw [← A.pool_of_vmPreserved hvm]
    apply SepWPpLscro.weaken_pre
      (P' := e2b301_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { sendingCt2 := hdr, uc := some uc } x.bs cur)
      (by dsimp only [e2b301_domLoopPre, chunkedCt2SampledPBCapAt,
            optCt2SentPBCapAt, unchunked2CapAt, sliceCursorAfter]; sep_entail)
    exact hcont _
      (by simp only [arm64_norm, wp_norm])
      (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htr])
      (by simp only [arm64_norm, wp_norm, hx19])
      (by simp only [arm64_norm, wp_norm, hx20])
      (by simp only [arm64_norm, wp_norm, hx21])
      (by simp only [arm64_norm, wp_norm, hx22])
      (by simp only [arm64_norm, wp_norm, hx23])
      (by simp only [arm64_norm, wp_norm, hx24])
      (by simp only [arm64_norm, wp_norm, hx25])
      ⟨by simp only [arm64_norm, wp_norm, hx27],
       by simp only [arm64_norm, wp_norm, hx28],
       by simp only [arm64_norm, wp_norm, hvregs]⟩


private theorem e2b301_dom_tag1_uc_enter [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {rest rest0 : List (BitVec 8)}
    {len : BitVec 64} {outerLimit : Nat} {evs : List AllocEvent}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hm_uc : m.uc = none)
    (hdv0 : decodeVarint rest = some (len, rest0))
    (hge_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ s'' : State,
      s''.pc = entry + 412#64 →
      s''.status = .Running → s''.sp = s0.sp - 128#64 → s''.trace = s0.trace →
      s''.readReg64 (Reg.gpr 19#5) = x.bufRef → s''.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s''.readReg64 (Reg.gpr 21#5) = x.slot →
      s''.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s''.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s''.readReg64 (Reg.gpr 24#5) = 1#64 →
      s''.readReg64 (Reg.gpr 25#5) = 8#64 →
      s''.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      ChunkedInl10CalleeSaved s0 s'' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s''
        (e2b301_domUcLoopPre A lim st evs s0 s'' x.msgPtr x.bufRef x.slot x.ptr
          m.sendingCt2 default x.bs rest0)
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (WireType.lengthDelimited).toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 1#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domLoopPre, chunkedCt2SampledPBCapAt, hm_uc,
      optCt2SentPBCapAt, memRegion_48_split_40_8 (x.msgPtr + 56#64),
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro v48
    wp_steps
    have hdef :
        ((x.msgPtr + 56#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          memRegion (x.msgPtr + 64#64) 40 ∗
          ((x.msgPtr + 104#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A.repAlloc (x.msgPtr + 56#64) rest.length
          (default : V1State.Unchunked.Ct2Sent).epoch
          (default : V1State.Unchunked.Ct2Sent).auth := by
      change ((x.msgPtr + 56#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        memRegion (x.msgPtr + 64#64) 40 ∗
        ((x.msgPtr + 104#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A.repAlloc (x.msgPtr + 56#64) rest.length 0#64 none
      simpa only [noneCap, arm64_norm] using
        default_unchunked2_entails_cap A.repAlloc (x.msgPtr + 56#64) rest.length
    apply SepWP.fold hdef (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 336#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b301_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        e2b301_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
    have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs rest0 :=
      suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hsub := bv_len_sub_limit hge_len
    apply sepWPpLscro_of_vm (mid := entry + 412#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b301_stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hevs_nil
      (conv => arg 4; rw [e2b301_stepEvents_nil])
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
      apply SepWP.fold
        (unchunked2CapAt_mono A.repAlloc (x.msgPtr + 56#64)
          (default : V1State.Unchunked.Ct2Sent).epoch
          (default : V1State.Unchunked.Ct2Sent).auth hrest0_le_rest)
        (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
      (conv => arg 4; simp only [sepConj_assoc])
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      let s_end : State :=
        ((((sm.writeReg64 (Reg.gpr 8#5) (BitVec.ofNat 64 rest0.length)).writeReg64 (Reg.gpr 26#5)
              (BitVec.ofNat 64 (rest0.length - len.toNat))).setPState
          (subsPState64 (BitVec.ofNat 64 rest0.length) len)).setPC (entry + 412#64))
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domUcLoopPre A lim st evs s0 s_end x.msgPtr x.bufRef x.slot x.ptr
          m.sendingCt2 default x.bs rest0)
        (by dsimp only [e2b301_domUcLoopPre, sliceCursorAfter, s_end];
            simp only [arm64_norm]; sep_entail)
      exact hcont s_end
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hrunm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hspm])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, htrm, htr])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx19_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx20_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx21_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx22_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx23_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx24_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx25_m])
        (by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hsm1, hsub])
        ⟨by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx27_m],
         by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hx28_m],
         by dsimp only [s_end]; simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b301_dom_tag2_poly_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {o₁ c₁ r₁ encOps maxOps : Nat}
    (hOps_poly : o₁ + encOps ≤ maxOps)
    (hCum_poly : c₁ + 342615 ≤ 345567)
    (hReq_poly : max r₁ 2560 ≤ 2560)
    (hPolyTightCall : subroutine_ok ((blkPC_301).rebase entry H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps))))
    {x : ChunkedCt2SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct2Sampled} {rest rest' : List (BitVec 8)}
    {d' : PolynomialEncoder} {outerLimit : Nat} {evs : List AllocEvent}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560))
    (hevs : SpqrTightEvs o₁ c₁ r₁ evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt56 : rest.length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hm_hdr : m.sendingCt2 = none)
    (hDom_poly : tlb_PolyEncoderDom ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot,
      x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length), rest⟩)
    (hpoly_res : (mergeMessage PolynomialEncoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (d', rest'))
    (hcont : ∀ (evs' : List AllocEvent) (s'' : State),
      SpqrTightEvs maxOps 345567 2560 evs' →
      s''.pc = entry + 168#64 →
      s''.status = .Running → s''.sp = s0.sp - 128#64 → s''.trace = s0.trace →
      s''.readReg64 (Reg.gpr 19#5) = x.bufRef → s''.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s''.readReg64 (Reg.gpr 21#5) = x.slot →
      s''.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s''.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
      s''.readReg64 (Reg.gpr 24#5) = 1#64 →
      s''.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s'' →
      SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s''
        (e2b301_domLoopPre A lim st evs' s0 s'' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingCt2 := some d' } x.bs rest')
        (WppPost
          (chunkedCt2SampledMergeSpecOfEnv A lim
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
            (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
          (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (WireType.lengthDelimited).toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_301).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b301_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
        (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyEncoderMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, restPtr, rest⟩
  have hpts_lt : (default : PolynomialEncoder).pts.length + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  have hpolys_lt : (default : PolynomialEncoder).polys.length + rest.length < 2 ^ 56 := by
    change 0 + rest.length < 2 ^ 56; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
  by_vm_steps
    (conv => arg 4; rw [e2b301_domLoopPre, chunkedCt2SampledPBCapAt, hm_hdr,
      optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split_inl x.msgPtr,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_eq_polyMerge s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm])
    apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
    apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
    apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
    wp_steps
    apply SepWP.fold (e2b301_default_polyEncoder_entails_zeroCap A.repAlloc x.msgPtr) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
      (ret_pc := entry + 288#64) hPolyTightCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [tlb_polyEncoderMergeTightSpecOfEnv, x_poly]
            rw [tlb_domHeap_of_dom hDom_poly]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx8, setWidth8_zext64_trunc32_ofNat64_wt_ct2],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hpts_lt,
        hpolys_lt,
        e2b301_fitsEnv_poly_tight hOps_poly hCum_poly hReq_poly hevs hDom_poly hFitTight⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv, polyEncoderMergeSpecOfEnv,
        PolyEncoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_p
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_p
      wp_focus_pure; intro hsm0
      (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
      have htight_p : SpqrTightEvs encOps 342615 2560 evs_p :=
        tlb_guardedEnv_tight_of_dom hDom_poly hevs_p
      have hevs' : SpqrTightEvs maxOps 345567 2560 (evs ++ evs_p) :=
        SpqrTightEvs.mono hOps_poly hCum_poly hReq_poly (hevs.append htight_p)
      (conv => arg 4; rw [e2b301_stepEvents_append])
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
      apply SepWP.fold (optCt2SentPBCapAt_mono A.repAlloc (x.msgPtr + 0x38#64) m.uc hrest'_le)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b301_domLoopPre A lim st (evs ++ evs_p) s0 _ x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingCt2 := some d' } x.bs rest')
        (by dsimp only [e2b301_domLoopPre, chunkedCt2SampledPBCapAt];
            rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
      exact hcont (evs ++ evs_p) _ hevs'
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m])
        (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m])
        (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

end Placed


/-! ## 6. `Dom`-Guarded Top-Level Proof & Exported Tight Contracts -/

private def e2b301_domOnlySpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedCt2SampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedCt2SampledDom x⌝ ∗
      (chunkedCt2SampledMergeSpecOfEnv A lim
        (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
        (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)).pre (x, st) s
  post := (chunkedCt2SampledMergeSpecOfEnv A lim
    (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
    (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)).post

private theorem e2b301_dom_only_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps encOps maxOps : Nat}
    (hOps : authOps + encOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hPolyTightCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps)))) :
    subroutine_ok ((blkPC_301).rebase (blkPl_301).base H)
      (blkPl_301).base
      (withLsCodeRoLoaded lsmpl (e2b301_domOnlySpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b301_domOnlySpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s0
    _
    (WppPost
      (chunkedCt2SampledMergeSpecOfEnv A lim
        (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
        (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
      (x, st) R s0)
    (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  intro hDom
  dsimp only [chunkedCt2SampledMergeSpecOfEnv]
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, hbound, hFit⟩
  have hDom0 := hDom
  rcases hDom with ⟨hwt_p, hmsg, pb, rest_end, ⟨hval_uc, hval_enc⟩, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := e2b301_wt_eq_lengthDelimited hwt_p
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by
    have hb := hbound.1
    rw [hmsg] at hb
    change 0 + x.bs.length < 2 ^ 56 at hb
    omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 345567 2560) :=
    fun evs h => hFit evs (Or.inl ⟨hDom0, h⟩)
  let rawTop : List (BitVec 8) := V1State.Chunked.Ct2Sampled.encodeRaw pb
  let rest0 : List (BitVec 8) := rawTop ++ rest_end
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 rawTop.length, rest0) := by
    rw [hbs_eq]; exact e2b301_lenPrefixed_decodeVarint rawTop rest_end
  have hrawTop_lt : rawTop.length + rest_end.length < x.bs.length := by
    rw [hbs_eq]; exact e2b301_lenPrefixed_length_gt rawTop rest_end
  have hrawTop_lt64 : rawTop.length < 2 ^ 64 := by omega
  have hlen0_toNat : (BitVec.ofNat 64 rawTop.length).toNat = rawTop.length :=
    Nat.mod_eq_of_lt hrawTop_lt64
  have hge_len0 : ¬ rest0.length < (BitVec.ofNat 64 rawTop.length).toNat := by
    dsimp only [rest0]; rw [List.length_append, hlen0_toNat]; omega
  have hout_lim : rest0.length - (BitVec.ofNat 64 rawTop.length).toNat = rest_end.length := by
    dsimp only [rest0]; rw [List.length_append, hlen0_toNat]; omega
  have hsome_top : (mergeMessage V1State.Chunked.Ct2Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, rest_end) := by
    rw [hwt_p, hmsg, hbs_eq]; exact e2b301_mergeMessage_ch_ct2Sampled pb rest_end hrawTop_lt64
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  refine e2b301_dom_prologue hVarintCall hpc hrun hsp_align hx0_wt hx1_msg hx2_buf
    hbs_lt hwt_ld hdv0 hge_len0 ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [hout_lim] at hx22_1
  let afterUc : List (BitVec 8) :=
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialEncoder.encodeRaw 2#32 pb.sendingCt2 ++ rest_end
  have hrest0_split : rest0 =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.Ct2Sent.encodeRaw 1#32 pb.uc ++ afterUc := by
    dsimp only [rest0, rawTop, afterUc]
    unfold V1State.Chunked.Ct2Sampled.encodeRaw
    simp only [List.append_assoc]
  have h_after_uc :
      ∀ (o₁ c₁ r₁ : Nat) (evs₁ : List AllocEvent) (s_u : State),
        o₁ + encOps ≤ maxOps → c₁ + 342615 ≤ 345567 → max r₁ 2560 ≤ 2560 →
        SpqrTightEvs o₁ c₁ r₁ evs₁ →
        afterUc.length ≤ x.bs.length → IsDropSuffix x.bs afterUc →
        s_u.pc = (blkPl_301).base + 168#64 →
        s_u.status = .Running → s_u.sp = s0.sp - 128#64 → s_u.trace = s0.trace →
        s_u.readReg64 (Reg.gpr 19#5) = x.bufRef → s_u.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s_u.readReg64 (Reg.gpr 21#5) = x.slot →
        s_u.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_end.length →
        s_u.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
        s_u.readReg64 (Reg.gpr 24#5) = 1#64 →
        s_u.readReg64 (Reg.gpr 25#5) = 8#64 →
        ChunkedInl10CalleeSaved s0 s_u →
        SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s_u
          (e2b301_domLoopPre A lim st evs₁ s0 s_u x.msgPtr x.bufRef x.slot x.ptr
            { sendingCt2 := none, uc := pb.uc } x.bs afterUc)
          (WppPost
            (chunkedCt2SampledMergeSpecOfEnv A lim
              (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
              (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
            (x, st) R s0)
          (WppPanicFalse R) := by
    intro o₁ c₁ r₁ evs₁ s_u hO₁ hC₁ hR₁ hevs₁ hafter_le hafter_suf
      hpc_u hrun_u hsp_u htr_u hx19_u hx20_u hx21_u hx22_u hx23_u hx24_u hx25_u hcs_u
    rcases henc : pb.sendingCt2 with _ | enc
    · have hafter_eq : afterUc = rest_end := by
        dsimp only [afterUc]; simp only [henc,
          CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
      have hpb_eq : ({ sendingCt2 := none, uc := pb.uc } : V1State.Chunked.Ct2Sampled) = pb := by
        cases pb; dsimp only at henc ⊢; subst henc; rfl
      rw [hafter_eq] at hafter_le hafter_suf ⊢
      rw [hpb_eq]
      have hevs_fin : SpqrTightEvs maxOps 345567 2560 evs₁ :=
        SpqrTightEvs.mono (by omega) (by omega) (by omega) hevs₁
      exact e2b301_dom_ok_exit hDom0 hsp_align rfl hafter_le hafter_suf hsome_top hevs_fin
        hpc_u hrun_u hsp_u htr_u hx21_u hx22_u hcs_u
    · let rest_poly : List (BitVec 8) :=
        tlb_lenPrefixed (PolynomialEncoder.encodeRaw enc) rest_end
      have hafter_eq : afterUc = 0x12#8 :: rest_poly := by
        dsimp only [afterUc, rest_poly]
        rw [henc]
        exact e2b301_encodeOptMessage_poly_tag2_some enc rest_end
      have hgt_poly : ¬ afterUc.length ≤ rest_end.length := by
        have hlt_p := e2b301_lenPrefixed_length_gt (PolynomialEncoder.encodeRaw enc) rest_end
        rw [hafter_eq, List.length_cons]
        dsimp only [rest_poly]; omega
      have hafter_lt : afterUc.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
      have hd_12 : decodeVarint afterUc = some (0x12#64, rest_poly) := by
        rw [hafter_eq]; exact e2b301_decodeVarint_0x12 rest_poly
      refine e2b301_dom_outer_decode_key hVarintCall hgt_poly hsp_align hafter_le hafter_lt
        hafter_suf hd_12 (by decide) (show WireType.ofNat? ((0x12#64).toNat % 8) =
          some .lengthDelimited by decide) (by decide) ?_
        hpc_u hrun_u hsp_u htr_u hx19_u hx20_u hx21_u hx22_u hx23_u hx24_u hx25_u hcs_u
      intro s_k hpc_k hrun_k hsp_k htr_k hx8_k hx1_k hx19_k hx20_k hx21_k hx22_k
        hx23_k hx24_k hx25_k hcs_k
      have hrp_le_a : rest_poly.length ≤ afterUc.length := Nat.le_of_lt (decodeVarint_length hd_12)
      have hrp_le : rest_poly.length ≤ x.bs.length := Nat.le_trans hrp_le_a hafter_le
      have hrp_lt56 : rest_poly.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrp_le hbs_lt56
      have hrp_suf : IsDropSuffix x.bs rest_poly :=
        suffix_trans hafter_le hafter_suf hrp_le_a (decodeVarint_suffix hd_12)
      have hraw_enc_lt : (PolynomialEncoder.encodeRaw enc).length < 2 ^ 64 := by
        have hlt_p := e2b301_lenPrefixed_length_gt (PolynomialEncoder.encodeRaw enc) rest_end
        dsimp only [rest_poly] at hrp_lt56; omega
      have hDom_poly : tlb_PolyEncoderDom ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot,
          x.ptr + BitVec.ofNat 64 (x.bs.length - rest_poly.length), rest_poly⟩ :=
        ⟨rfl, rfl, enc, rest_end, hval_enc enc henc, rfl⟩
      have hpoly_res : (mergeMessage PolynomialEncoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest_poly 98).toOption =
          some (enc, rest_end) :=
        e2b301_mergeMessage_polyEncoder enc rest_end hraw_enc_lt
      have hx1_k2 : s_k.readReg64 (Reg.gpr 1#5) = 2#64 := hx1_k
      refine e2b301_dom_tag2_poly_step hO₁ hC₁ hR₁ hPolyTightCall hFitTight hevs₁ hsp_align
        hrp_le hrp_lt56 hrp_suf rfl hDom_poly hpoly_res ?_
        hpc_k hrun_k hsp_k htr_k hx8_k hx1_k2 hx19_k hx20_k hx21_k hx22_k
        hx23_k hx24_k hx25_k hcs_k
      intro evs₂ s_p hevs₂ hpc_p hrun_p hsp_p htr_p hx19_p hx20_p hx21_p hx22_p
        hx23_p hx24_p hx25_p hcs_p
      have hpf := proto_mergeMessage_suffix hpoly_res
      have hrend_le : rest_end.length ≤ x.bs.length := Nat.le_trans hpf.1 hrp_le
      have hrend_suf : IsDropSuffix x.bs rest_end := suffix_trans hrp_le hrp_suf hpf.1 hpf.2
      have hpb_eq : ({ sendingCt2 := some enc, uc := pb.uc } : V1State.Chunked.Ct2Sampled) = pb := by
        cases pb; dsimp only at henc ⊢; subst henc; rfl
      rw [hpb_eq]
      exact e2b301_dom_ok_exit hDom0 hsp_align rfl hrend_le hrend_suf hsome_top hevs₂
        hpc_p hrun_p hsp_p htr_p hx21_p hx22_p hcs_p
  rw [hmsg]
  rcases huc : pb.uc with _ | u
  · have hrest0_eq : rest0 = afterUc := by
      rw [hrest0_split, huc]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
    have hm0_eq : (default : V1State.Chunked.Ct2Sampled) = { sendingCt2 := none, uc := pb.uc } := by
      rw [huc]; rfl
    rw [hrest0_eq] at hrest0_le hrest0_suf ⊢
    rw [hm0_eq]
    exact h_after_uc 0 0 0 [] s1 (by omega) (by decide) (by decide) (SpqrTightEvs.nil 0 0 0)
      hrest0_le hrest0_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1 hcs1
  · let rawU : List (BitVec 8) := V1State.Unchunked.Ct2Sent.encodeRaw u
    let rest_uc : List (BitVec 8) := tlb_lenPrefixed rawU afterUc
    let uc0_bytes : List (BitVec 8) := rawU ++ afterUc
    have hrest0_eq : rest0 = 0x0a#8 :: rest_uc := by
      rw [hrest0_split, huc]
      exact e2b301_encodeOptMessage_uc_tag1_some u afterUc
    have hafterUc_ge_end : rest_end.length ≤ afterUc.length := by
      dsimp only [afterUc]; rw [List.length_append]; omega
    have hgt_uc : ¬ rest0.length ≤ rest_end.length := by
      have hlt_u := e2b301_lenPrefixed_length_gt rawU afterUc
      rw [hrest0_eq, List.length_cons]
      dsimp only [rest_uc] at *; omega
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hd_0a : decodeVarint rest0 = some (0x0a#64, rest_uc) := by
      rw [hrest0_eq]; exact e2b301_decodeVarint_0x0a rest_uc
    refine e2b301_dom_outer_decode_key hVarintCall hgt_uc hsp_align hrest0_le hrest0_lt
      hrest0_suf hd_0a (by decide) (show WireType.ofNat? ((0x0a#64).toNat % 8) =
        some .lengthDelimited by decide) (by decide) ?_
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    intro s_k1 hpc_k1 hrun_k1 hsp_k1 htr_k1 hx8_k1 hx1_k1 hx19_k1 hx20_k1 hx21_k1 hx22_k1
      hx23_k1 hx24_k1 hx25_k1 hcs_k1
    have hruc_le_r0 : rest_uc.length ≤ rest0.length := Nat.le_of_lt (decodeVarint_length hd_0a)
    have hruc_le : rest_uc.length ≤ x.bs.length := Nat.le_trans hruc_le_r0 hrest0_le
    have hruc_lt : rest_uc.length < 2 ^ 63 := Nat.lt_of_le_of_lt hruc_le hbs_lt
    have hruc_suf : IsDropSuffix x.bs rest_uc :=
      suffix_trans hrest0_le hrest0_suf hruc_le_r0 (decodeVarint_suffix hd_0a)
    have hdv_uc : decodeVarint rest_uc = some (BitVec.ofNat 64 rawU.length, uc0_bytes) :=
      e2b301_lenPrefixed_decodeVarint rawU afterUc
    have hrawU_lt : rawU.length + afterUc.length < rest_uc.length :=
      e2b301_lenPrefixed_length_gt rawU afterUc
    have hrawU_lt64 : rawU.length < 2 ^ 64 := by omega
    have hlenU_toNat : (BitVec.ofNat 64 rawU.length).toNat = rawU.length :=
      Nat.mod_eq_of_lt hrawU_lt64
    have hge_lenU : ¬ uc0_bytes.length < (BitVec.ofNat 64 rawU.length).toNat := by
      dsimp only [uc0_bytes]; rw [List.length_append, hlenU_toNat]; omega
    have hin_lim : uc0_bytes.length - (BitVec.ofNat 64 rawU.length).toNat = afterUc.length := by
      dsimp only [uc0_bytes]; rw [List.length_append, hlenU_toNat]; omega
    have hx1_k1' : s_k1.readReg64 (Reg.gpr 1#5) = 1#64 := hx1_k1
    refine e2b301_dom_tag1_uc_enter hVarintCall hsp_align hbs_lt hruc_le hruc_lt hruc_suf
      rfl hdv_uc hge_lenU ?_
      hpc_k1 hrun_k1 hsp_k1 htr_k1 hx8_k1 hx1_k1' hx19_k1 hx20_k1 hx21_k1 hx22_k1
      hx23_k1 hx24_k1 hx25_k1 hcs_k1
    intro s_uc0 hpc_uc0 hrun_uc0 hsp_uc0 htr_uc0 hx19_uc0 hx20_uc0 hx21_uc0 hx22_uc0
      hx23_uc0 hx24_uc0 hx25_uc0 hx26_uc0 hcs_uc0
    rw [hin_lim] at hx26_uc0
    have huc0_le_ruc : uc0_bytes.length ≤ rest_uc.length := Nat.le_of_lt (decodeVarint_length hdv_uc)
    have huc0_le : uc0_bytes.length ≤ x.bs.length := Nat.le_trans huc0_le_ruc hruc_le
    have huc0_suf : IsDropSuffix x.bs uc0_bytes :=
      suffix_trans hruc_le hruc_suf huc0_le_ruc (decodeVarint_suffix hdv_uc)
    let afterEpoch : List (BitVec 8) :=
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 u.auth ++ afterUc
    have huc0_split : uc0_bytes =
        (if u.epoch == 0#64 then []
         else 0x08#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch) ++
          afterEpoch :=
      e2b301_ct2Sent_encodeRaw_split u afterUc
    have h_after_epoch :
        ∀ s_ae : State,
          afterEpoch.length ≤ x.bs.length → IsDropSuffix x.bs afterEpoch →
          s_ae.pc = (blkPl_301).base + 412#64 →
          s_ae.status = .Running → s_ae.sp = s0.sp - 128#64 → s_ae.trace = s0.trace →
          s_ae.readReg64 (Reg.gpr 19#5) = x.bufRef → s_ae.readReg64 (Reg.gpr 20#5) = x.msgPtr →
          s_ae.readReg64 (Reg.gpr 21#5) = x.slot →
          s_ae.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_end.length →
          s_ae.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 →
          s_ae.readReg64 (Reg.gpr 24#5) = 1#64 →
          s_ae.readReg64 (Reg.gpr 25#5) = 8#64 →
          s_ae.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 afterUc.length →
          ChunkedInl10CalleeSaved s0 s_ae →
          SepWPpLscro lsmpl ((blkPC_301).rebase (blkPl_301).base H) (s0.readReg64 Reg.lr) s_ae
            (e2b301_domUcLoopPre A lim st [] s0 s_ae x.msgPtr x.bufRef x.slot x.ptr
              none { epoch := u.epoch, auth := none } x.bs afterEpoch)
            (WppPost
              (chunkedCt2SampledMergeSpecOfEnv A lim
                (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
                (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))
              (x, st) R s0)
            (WppPanicFalse R) := by
      intro s_ae hae_le hae_suf hpc_ae hrun_ae hsp_ae htr_ae hx19_ae hx20_ae hx21_ae
        hx22_ae hx23_ae hx24_ae hx25_ae hx26_ae hcs_ae
      have hval_u := hval_uc u huc
      rcases hauth : u.auth with _ | auth
      · have hae_eq : afterEpoch = afterUc := by
          dsimp only [afterEpoch]; simp only [hauth,
            CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
        have hu_eq : ({ epoch := u.epoch, auth := none } : V1State.Unchunked.Ct2Sent) = u := by
          cases u; dsimp only at hauth ⊢; subst hauth; rfl
        rw [hae_eq] at hae_le hae_suf ⊢
        rw [hu_eq]
        refine e2b301_dom_uc_exit rfl hae_le hae_suf ?_
          hpc_ae hrun_ae hsp_ae htr_ae hx19_ae hx20_ae hx21_ae hx22_ae
          hx23_ae hx24_ae hx25_ae hx26_ae hcs_ae
        intro s_ux hpc_ux hrun_ux hsp_ux htr_ux hx19_ux hx20_ux hx21_ux hx22_ux
          hx23_ux hx24_ux hx25_ux hcs_ux
        have hm_uc_eq : ({ sendingCt2 := none, uc := some u } : V1State.Chunked.Ct2Sampled) =
            { sendingCt2 := none, uc := pb.uc } := by rw [huc]
        rw [hm_uc_eq]
        exact h_after_uc 0 0 0 [] s_ux (by omega) (by decide) (by decide) (SpqrTightEvs.nil 0 0 0)
          hae_le hae_suf hpc_ux hrun_ux hsp_ux htr_ux hx19_ux hx20_ux hx21_ux hx22_ux
          hx23_ux hx24_ux hx25_ux hcs_ux
      · let rest_auth : List (BitVec 8) :=
          tlb_lenPrefixed (ProtoAuthenticator.encodeRaw auth) afterUc
        have hae_eq : afterEpoch = 0x12#8 :: rest_auth := by
          dsimp only [afterEpoch, rest_auth]
          rw [hauth]
          exact e2b301_encodeOptMessage_auth_tag2_some auth afterUc
        have hgt_auth : ¬ afterEpoch.length ≤ afterUc.length := by
          have hlt_a := e2b301_lenPrefixed_length_gt (ProtoAuthenticator.encodeRaw auth) afterUc
          rw [hae_eq, List.length_cons]
          dsimp only [rest_auth]; omega
        have hae_lt : afterEpoch.length < 2 ^ 63 := Nat.lt_of_le_of_lt hae_le hbs_lt
        have hd_a12 : decodeVarint afterEpoch = some (0x12#64, rest_auth) := by
          rw [hae_eq]; exact e2b301_decodeVarint_0x12 rest_auth
        refine e2b301_dom_uc_decode_key hVarintCall hgt_auth hsp_align hae_le hae_lt hae_suf
          hd_a12 (by decide) (show WireType.ofNat? ((0x12#64).toNat % 8) =
            some .lengthDelimited by decide) (by decide) ?_
          hpc_ae hrun_ae hsp_ae htr_ae hx19_ae hx20_ae hx21_ae hx22_ae
          hx23_ae hx24_ae hx25_ae hx26_ae hcs_ae
        intro s_ak hpc_ak hrun_ak hsp_ak htr_ak hx0_ak hx1_ak hx19_ak hx20_ak hx21_ak
          hx22_ak hx23_ak hx24_ak hx25_ak hx26_ak hcs_ak
        have hra_le_ae : rest_auth.length ≤ afterEpoch.length :=
          Nat.le_of_lt (decodeVarint_length hd_a12)
        have hra_le : rest_auth.length ≤ x.bs.length := Nat.le_trans hra_le_ae hae_le
        have hra_lt : rest_auth.length < 2 ^ 63 := Nat.lt_of_le_of_lt hra_le hbs_lt
        have hra_suf : IsDropSuffix x.bs rest_auth :=
          suffix_trans hae_le hae_suf hra_le_ae (decodeVarint_suffix hd_a12)
        have hraw_auth_lt : (ProtoAuthenticator.encodeRaw auth).length < 2 ^ 64 := by
          have hlt_a := e2b301_lenPrefixed_length_gt (ProtoAuthenticator.encodeRaw auth) afterUc
          dsimp only [rest_auth] at hra_lt; omega
        have hDom_auth : tlb_AuthDom ⟨.lengthDelimited, x.msgPtr + 0x38#64, default,
            x.bufRef, x.slot, x.ptr + BitVec.ofNat 64 (x.bs.length - rest_auth.length),
            rest_auth⟩ :=
          ⟨rfl, rfl, auth, afterUc, hval_u auth hauth, rfl⟩
        have hauth_res : (mergeMessage ProtoAuthenticator.mergeField
            (codecWireTypeToProto .lengthDelimited) default rest_auth 97).toOption =
            some (auth, afterUc) :=
          e2b301_mergeMessage_auth auth afterUc hraw_auth_lt
        have hx1_ak2 : s_ak.readReg64 (Reg.gpr 1#5) = 2#64 := hx1_ak
        refine e2b301_dom_uc_auth_step (by omega) hAuthTightCall hFitTight
          (SpqrTightEvs.nil 0 0 0) hsp_align hra_le hra_lt hra_suf rfl hDom_auth hauth_res ?_
          hpc_ak hrun_ak hsp_ak htr_ak hx0_ak hx1_ak2 hx19_ak hx20_ak hx21_ak hx22_ak
          hx23_ak hx24_ak hx25_ak hx26_ak hcs_ak
        intro evs_a s_ad hevs_a hpc_ad hrun_ad hsp_ad htr_ad hx19_ad hx20_ad hx21_ad
          hx22_ad hx23_ad hx24_ad hx25_ad hx26_ad hcs_ad
        have haf := proto_mergeMessage_suffix hauth_res
        have hauc_le : afterUc.length ≤ x.bs.length := Nat.le_trans haf.1 hra_le
        have hauc_suf : IsDropSuffix x.bs afterUc := suffix_trans hra_le hra_suf haf.1 haf.2
        have hu_eq : ({ epoch := u.epoch, auth := some auth } : V1State.Unchunked.Ct2Sent) = u := by
          cases u; dsimp only at hauth ⊢; subst hauth; rfl
        rw [hu_eq]
        refine e2b301_dom_uc_exit rfl hauc_le hauc_suf ?_
          hpc_ad hrun_ad hsp_ad htr_ad hx19_ad hx20_ad hx21_ad hx22_ad
          hx23_ad hx24_ad hx25_ad hx26_ad hcs_ad
        intro s_ux hpc_ux hrun_ux hsp_ux htr_ux hx19_ux hx20_ux hx21_ux hx22_ux
          hx23_ux hx24_ux hx25_ux hcs_ux
        have hm_uc_eq : ({ sendingCt2 := none, uc := some u } : V1State.Chunked.Ct2Sampled) =
            { sendingCt2 := none, uc := pb.uc } := by rw [huc]
        rw [hm_uc_eq]
        exact h_after_uc authOps 2952 32 evs_a s_ux hOps (by decide) (by decide) hevs_a
          hauc_le hauc_suf hpc_ux hrun_ux hsp_ux htr_ux hx19_ux hx20_ux hx21_ux hx22_ux
          hx23_ux hx24_ux hx25_ux hcs_ux
    cases he0 : (u.epoch == 0#64)
    · let ep_bytes : List (BitVec 8) :=
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch ++ afterEpoch
      have huc0_eq : uc0_bytes = 0x08#8 :: ep_bytes := by
        rw [huc0_split, he0]; simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append]; rfl
      have hae_ge_auc : afterUc.length ≤ afterEpoch.length := by
        rw [show afterEpoch.length =
          (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            ProtoAuthenticator.encodeRaw 2#32 u.auth).length + afterUc.length
          from List.length_append]
        omega
      have hgt_ep : ¬ uc0_bytes.length ≤ afterUc.length := by
        rw [huc0_eq, List.length_cons]
        dsimp only [ep_bytes]; rw [List.length_append]; omega
      have huc0_lt : uc0_bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt huc0_le hbs_lt
      have hd_08 : decodeVarint uc0_bytes = some (0x08#64, ep_bytes) := by
        rw [huc0_eq]; exact e2b301_decodeVarint_0x08 ep_bytes
      refine e2b301_dom_uc_decode_key hVarintCall hgt_ep hsp_align huc0_le huc0_lt huc0_suf
        hd_08 (by decide) (show WireType.ofNat? ((0x08#64).toNat % 8) =
          some .varint by decide) (by decide) ?_
        hpc_uc0 hrun_uc0 hsp_uc0 htr_uc0 hx19_uc0 hx20_uc0 hx21_uc0 hx22_uc0
        hx23_uc0 hx24_uc0 hx25_uc0 hx26_uc0 hcs_uc0
      intro s_ek hpc_ek hrun_ek hsp_ek htr_ek hx0_ek hx1_ek hx19_ek hx20_ek hx21_ek
        hx22_ek hx23_ek hx24_ek hx25_ek hx26_ek hcs_ek
      have hep_le_uc0 : ep_bytes.length ≤ uc0_bytes.length :=
        Nat.le_of_lt (decodeVarint_length hd_08)
      have hep_le : ep_bytes.length ≤ x.bs.length := Nat.le_trans hep_le_uc0 huc0_le
      have hep_lt : ep_bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hep_le hbs_lt
      have hep_suf : IsDropSuffix x.bs ep_bytes :=
        suffix_trans huc0_le huc0_suf hep_le_uc0 (decodeVarint_suffix hd_08)
      have hdv_ep : decodeVarint ep_bytes = some (u.epoch, afterEpoch) :=
        e2b301_decodeVarint_protoVarint u.epoch afterEpoch
      have hx0_ek0 : s_ek.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_ek
      have hx1_ek1 : s_ek.readReg64 (Reg.gpr 1#5) = 1#64 := hx1_ek
      refine e2b301_dom_uc_epoch_step hVarintCall hsp_align hep_le hep_lt hep_suf hdv_ep ?_
        hpc_ek hrun_ek hsp_ek htr_ek hx0_ek0 hx1_ek1 hx19_ek hx20_ek hx21_ek hx22_ek
        hx23_ek hx24_ek hx25_ek hx26_ek hcs_ek
      intro s_ae hpc_ae hrun_ae hsp_ae htr_ae hx19_ae hx20_ae hx21_ae hx22_ae
        hx23_ae hx24_ae hx25_ae hx26_ae hcs_ae
      have hae_le_ep : afterEpoch.length ≤ ep_bytes.length :=
        Nat.le_of_lt (decodeVarint_length hdv_ep)
      have hae_le : afterEpoch.length ≤ x.bs.length := Nat.le_trans hae_le_ep hep_le
      have hae_suf : IsDropSuffix x.bs afterEpoch :=
        suffix_trans hep_le hep_suf hae_le_ep (decodeVarint_suffix hdv_ep)
      exact h_after_epoch s_ae hae_le hae_suf hpc_ae hrun_ae hsp_ae htr_ae
        hx19_ae hx20_ae hx21_ae hx22_ae hx23_ae hx24_ae hx25_ae hx26_ae hcs_ae
    · have he_eq : u.epoch = 0#64 := beq_iff_eq.mp he0
      have huc0_eq : uc0_bytes = afterEpoch := by
        rw [huc0_split, he0]; simp only [↓reduceIte, List.nil_append]
      have hdef_eq : (default : V1State.Unchunked.Ct2Sent) =
          { epoch := u.epoch, auth := none } := by rw [he_eq]; rfl
      rw [huc0_eq] at huc0_le huc0_suf ⊢
      rw [hdef_eq]
      exact h_after_epoch s_uc0 huc0_le huc0_suf hpc_uc0 hrun_uc0 hsp_uc0 htr_uc0
        hx19_uc0 hx20_uc0 hx21_uc0 hx22_uc0 hx23_uc0 hx24_uc0 hx25_uc0 hx26_uc0 hcs_uc0


/-- Block `301` (`V1State.Chunked.Ct2Sampled::merge`) guarded-tight contract on
`(blkPC_301).rebase (blkPl_301).base H`: composes any tight `ProtoAuthenticator::merge`
(`Block 295`, over `tlb_authMergeTightSpecOfEnv` / `tlb_AuthGuardedEnvOf authOps`) and tight
`PolynomialEncoder::merge` (`Block 297`, over `tlb_polyEncoderMergeTightSpecOfEnv` /
`tlb_PolyEncoderGuardedEnvOf encOps`) into `tlb_ChunkedCt2SampledGuardedEnvOf maxOps` whenever
`authOps + encOps ≤ maxOps`. -/
theorem e2b301_chunkedCt2Sampled_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {authOps encOps maxOps : Nat}
    (hOps : authOps + encOps ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hPolyTightCall : subroutine_ok ((blkPC_301).rebase (blkPl_301).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps)))) :
    subroutine_ok ((blkPC_301).rebase (blkPl_301).base H)
      (blkPl_301).base
      (withLsCodeRoLoaded lsmpl
        (chunkedCt2SampledMergeSpecOfEnv A lim
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps)
          (tlb_ChunkedCt2SampledGuardedEnvOf maxOps))) := by
  have hDomOk := e2b301_dom_only_subroutine_ok hOps hVarintCall hAuthTightCall hPolyTightCall
  have hKleene := chunked_ct2_sampled_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hAuthCall hPolyCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : tlb_ChunkedCt2SampledDom x.1
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2b301_domOnlySpec A lim maxOps)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2b301_domOnlySpec]
      exact sepConj_mono_left (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _)))
    exact hDomOk.mono_outcome x R s0 hpc hrun hpre_dom hsp fun _ out => out
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (chunkedCt2SampledMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, chunkedCt2SampledMergeSpec, chunkedCt2SampledMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun hp =>
        Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩ (Entails.refl _)
      exact tlb_fitsEnv_fallback_of_not_dom hDom hp.2.2.2.2
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, chunkedCt2SampledMergeSpec, chunkedCt2SampledMergeSpecOfEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, chunkedCt2SampledMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, chunkedCt2SampledMergeSpec,
        chunkedCt2SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt2SampledMergeSpec,
        chunkedCt2SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedCt2SampledMergeSpec,
        chunkedCt2SampledMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-- `withLsCodeRoLoaded` variant of `e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of` producing
`tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim maxOps ext`. -/
theorem e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of_cro [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim maxOps ext := by
  have hok := e2b301_chunkedCt2Sampled_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext) hOps
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase
        (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase
        (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase
        (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase
        (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase
        (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthBase)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase
        (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncBase)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase
        (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthTight)
    (e2b301_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase
        (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncTight)
  rw [IsLsBlockProg.eq_blockProgram
        (prog := (blkPC_301).rebase (blkPl_301).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 301)] at hok
  exact hok

/-- Guarded-tight contract `tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim maxOps ext` on Block `301` (`authOps + encOps ≤ maxOps`). -/
theorem e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedCt2SampledMergePlacedTightOkOf A lim maxOps ext :=
  e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of_cro hOps
    (e2b301_subroutine_ok_cro_of_cl hFrom)
    (e2b301_subroutine_ok_cro_of_cl hPush)
    (e2b301_subroutine_ok_cro_of_cl hVarint)
    (e2b301_subroutine_ok_cro_of_cl hSkip)
    hAuthBase hPolyEncBase hAuthTight hPolyEncTight

/-- Default `maxOps = 39` (`4 + 35`) specialization proving `tlb_ChunkedCt2SampledMergePlacedTightOk`. -/
theorem e2b301_chunkedCt2Sampled_merge_placed_tight_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedCt2SampledMergePlacedTightOk A lim ext :=
  e2b301_chunkedCt2Sampled_merge_placed_tight_ok_of (Nat.le_refl 39)
    hFrom hPush hVarint hSkip hAuthBase hPolyEncBase hAuthTight hPolyEncTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB301PlacedBudget
