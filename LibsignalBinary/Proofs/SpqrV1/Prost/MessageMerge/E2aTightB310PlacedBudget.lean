/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.EkReceivedCt1Sampled::merge` (Block `310`)

Proves `tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf` on Block `310` within
`SpqrTightEvs maxOps 404301 2560` (`authOps + 6 + encOps ≤ maxOps`, default `45 = 4 + 6 + 35`:
inlined `Unchunked.Ct1SentEkReceived` `61,686` B + `PolynomialEncoder` `342,615` B) on canonical
`tlb_ChunkedEkReceivedCt1SampledDom` inputs, falling back to `ChunkedEkReceivedCt1SampledMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB310PlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261
   instIsLsBlockProg_263 instIsLsBlockProg_290 instIsLsBlockProg_291 instIsLsBlockProg_295
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem PqRatchetState V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeState)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedEkReceivedCt1SampledMergeGhost codecWireTypeToProto instIsLsBlockProg_297)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkPC_310 blkPl_310 instIsLsBlockProg_310)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedEkReceivedCt1SampledDom tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf
   tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk
   tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf
   tlb_GuardedEnv tlb_PolyEncoderDom tlb_PolyEncoderMergePlacedTightOkOf
   tlb_ValidChunkedEkReceivedCt1SampledPB tlb_ValidPqRatchetStatePB
   tlb_authMergeTightSpecOfEnv tlb_fitsEnv_fallback_of_not_dom
   tlb_guardedEnv_tight_of_dom tlb_lenPrefixed tlb_polyEncoderMergeTightSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeEnv authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledClPlacedBudget
  (chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedEkReceivedCt1SampledMergeEnv chunkedEkReceivedCt1SampledMergePostEnv_imp_pre
   chunkedEkReceivedCt1SampledMergeSpec chunkedEkReceivedCt1SampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergeEnv bytesMerge3RawBudgetSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

/-! ## 1. Own-Block ↔ Caller-Block Transfer Helpers (`e2b310_`) -/

private class e2b310_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 290 :=
  ⟨by decide, by decide, (instIsLsBlockProg_290 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 297 :=
  ⟨by decide, by decide, (instIsLsBlockProg_297 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b310_IsLsValidBlock 310 :=
  ⟨by decide, by decide, (instIsLsBlockProg_310 (fun _ => none)).externs_eq⟩

private theorem e2b310_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2b310_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s0.mem :=
    hfr0.1 j hj.lt_blocks hj.not_mutated H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc = callerProg.externAt? pc :=
    fun pc => by
      rw [hcaller.eq_blockProgram,
        ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
          (hj.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem e2b310_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2b310_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2b310_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2b310_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Fully Parametric Guarded-Tight Envelope & `TopStateTight` Bridge -/

/-- Own `bytes::merge` non-free op count inside Block `310`'s inlined `Unchunked.Ct1SentEkReceived`
(`es`, `ek`, `ct1`: `3` `bytes` fields × `2` non-free ops via `bytesMergeEventsCore`). -/
abbrev e2b310_ownBytesOps : Nat := 6

/-- Own `bytes::merge` cumulative `spqrTraceTightCost` cap inside Block `310`
(`es ≤ 2,080`, `ek ≤ 1,152`, `ct1 ≤ 960`: `3 × (2 × 9,789) = 58,734` B). -/
abbrev e2b310_ownBytesCum : Nat := 58734

/-- Maximum single-allocation request among Block `310`'s own `bytes` fields
(`max 2080 (max 1152 960) = 2080` B). -/
abbrev e2b310_ownBytesMaxReq : Nat := 2080

/-- Parametric guarded-tight envelope for Block `310` (`PreEnv = PostEnv`):
enforces `SpqrTightEvs maxOps cumCap maxReq evs` on `tlb_ChunkedEkReceivedCt1SampledDom x`, and
falls back to `ChunkedEkReceivedCt1SampledMergeEnv x evs` on `¬ tlb_ChunkedEkReceivedCt1SampledDom x`.
At `(maxOps, 404301, 2560)` this is definitionally `tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf maxOps`. -/
def e2b310_ChunkedEkReceivedCt1SampledGuardedEnv (maxOps cumCap maxReq : Nat) :
    ChunkedEkReceivedCt1SampledMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedEkReceivedCt1SampledDom
    (SpqrTightEvs maxOps cumCap maxReq) ChunkedEkReceivedCt1SampledMergeEnv

theorem e2b310_guardedEnv_eq_tlb (maxOps : Nat) :
    e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps 404301 2560 =
      tlb_ChunkedEkReceivedCt1SampledGuardedEnvOf maxOps := rfl

/-- Extracts `SpqrTightEvs maxOps cumCap maxReq evs` from `e2b310_ChunkedEkReceivedCt1SampledGuardedEnv`
when the serialized state bytes satisfy `TopStateTight` (`tlb_ValidPqRatchetStatePB`). -/
theorem e2b310_guardedEnv_sub_tight_of_topStateTight
    {F : ShaCompress} {K : MlKem} {stateBytes : Bytes}
    {maxOps cumCap maxReq : Nat}
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {evs : List AllocEvent}
    (_hTop : LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux.TopStateTight F K stateBytes)
    (hPb : ∃ topPb : PqRatchetState, stateBytes = encodeState topPb ∧ tlb_ValidPqRatchetStatePB topPb ∧
      ∃ v1 ck rest,
        topPb.inner = some (.v1 v1) ∧
        v1.innerState = some (.ekReceivedCt1Sampled ck) ∧
        codecWireTypeToProto x.wt = .lengthDelimited ∧
        x.msg = default ∧
        x.bs = tlb_lenPrefixed (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ck) rest)
    (hEnv : e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq x evs) :
    SpqrTightEvs maxOps cumCap maxReq evs := by
  rcases hPb with ⟨topPb, _, hValidTop, v1, ck, rest, hInner, hIs, hWt, hMsg, hBs⟩
  have hValidCk : tlb_ValidChunkedEkReceivedCt1SampledPB ck :=
    hValidTop.2.2 v1 hInner (.ekReceivedCt1Sampled ck) hIs
  have hDom : tlb_ChunkedEkReceivedCt1SampledDom x :=
    ⟨hWt, hMsg, ck, rest, hValidCk, hBs⟩
  exact tlb_guardedEnv_tight_of_dom hDom hEnv

/-! ## 3. Parametric Guarded-Tight Contract on `(blkPC_310).rebase (blkPl_310).base` -/

section DomProof

set_option linter.unusedSimpArgs false

open ProofLib.ProgramReflection
open CryptoVerification.RustHeap
  (RustAlloc vecAt vecBuf vecHeader vecU8At vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix bv32_zeroExtend_ofNat bytesMergeCapOk_zero
   decodeVarint_suffix key_shr32_of_lt key_wt_some pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authenticatorPBCapAt memRegion_40_cells optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderAt protoPolynomialEncoderPinnedAt protoPolynomialEncoderPolysOff)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedInl10CalleeSaved OptPolyEncoderBound PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedEkReceivedCt1SampledMerge_fnOff chunkedEkReceivedCt1SampledPBCapAt
   chunkedEkReceivedCt1SampledPBCapAt_mono chunkedInlBelowStack
   chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails
   chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_eq_polyMerge chunkedInlSavedRegs10 chunkedInlStack
   cmp_len_limit_of_eq cmp_len_limit_of_gt
   memRegion_polyEncoder_none_split_inl mergeBytes_length mergeBytes_suffix
   optCt1SentEkReceivedPBCapAt optCt1SentEkReceivedPBCapAt_mono
   optPolynomialEncoderPBAt_some_eq polyEncoderToProto proto_mergeMessage_suffix
   stackAt_chunkedInl10_epilogue stackAt_chunkedInl_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp unchunked5CapAt withLscroProp
   wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_authenticator loopsTo_ch_ekReceivedCt1Sampled loopsTo_polyEncoder
   mergeMessage_encode proto_decodeVarint_encodeVarint)
open LibsignalBinary.Heap
  (VmPreserved fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ValidAuthPB tlb_ValidPolyEncoderPB tlb_ValidUcCt1SentEkReceivedPB
   tlb_authenticatorZeroCapAt tlb_domHeap_of_dom tlb_fitsEnv_guarded_of_dom
   tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (AuthMergePostEnv authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (BytesMerge3EnvCore)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledUcBudgetAux
  (unchunked5CapAt_eq vecU8At_entails_vecU8CapAtEk vecU8CapAtEk vecU8CapAtEk_mono)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedEkReceivedCt1SampledMergePostEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env PolyEncoderMergePostEnv polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (DecodeVarint2Env decodeVarint2SpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
  chunkedEkReceivedCt1SampledMerge_fnOff

private theorem e2b310_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem e2b310_setWidth8_zext64_trunc32_ofNat64_wt (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) =
      BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

private theorem e2b310_vecU8CapAtEk_unfold (A : RustAlloc) (a : BitVec 64) (bsLen : Nat)
    (bs : List (BitVec 8)) :
    vecU8CapAtEk A a bsLen bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap bsLen⌝ ∗ vecU8At A a cap ptr bs := rfl

private theorem e2b310_memRegion_unchunked5_none_split (a : BitVec 64) :
    memRegion (a + 8#64) 120 =
      ∃∗ v120 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
      ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
      ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((a + 8#64) ↦₆₄ v8) ∗ ((a + 16#64) ↦₆₄ v16) ∗ ((a + 24#64) ↦₆₄ v24) ∗
        ((a + 32#64) ↦₆₄ v32) ∗ ((a + 40#64) ↦₆₄ v40) ∗ ((a + 48#64) ↦₆₄ v48) ∗
        ((a + 56#64) ↦₆₄ v56) ∗ ((a + 64#64) ↦₆₄ v64) ∗ ((a + 72#64) ↦₆₄ v72) ∗
        memRegion (a + 80#64) 40 ∗ ((a + 120#64) ↦₆₄ v120) := by
  have s1 := memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 112) (N := 120) rfl (by bv_omega) (by decide)
  have s2 := memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 104) (N := 112) rfl (by bv_omega) (by decide)
  have s3 := memRegion_split' (b := a + 24#64) (b' := a + 32#64) (n := 8) (k := 96) (N := 104) rfl (by bv_omega) (by decide)
  have s4 := memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 88) (N := 96) rfl (by bv_omega) (by decide)
  have s5 := memRegion_split' (b := a + 40#64) (b' := a + 48#64) (n := 8) (k := 80) (N := 88) rfl (by bv_omega) (by decide)
  have s6 := memRegion_split' (b := a + 48#64) (b' := a + 56#64) (n := 8) (k := 72) (N := 80) rfl (by bv_omega) (by decide)
  have s7 := memRegion_split' (b := a + 56#64) (b' := a + 64#64) (n := 8) (k := 64) (N := 72) rfl (by bv_omega) (by decide)
  have s8 := memRegion_split' (b := a + 64#64) (b' := a + 72#64) (n := 8) (k := 56) (N := 64) rfl (by bv_omega) (by decide)
  have s9 := memRegion_split' (b := a + 72#64) (b' := a + 80#64) (n := 8) (k := 48) (N := 56) rfl (by bv_omega) (by decide)
  have s10 := memRegion_split' (b := a + 80#64) (b' := a + 120#64) (n := 40) (k := 8) (N := 48) rfl (by bv_omega) (by decide)
  rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    ProofLib.memRegion_eight (a + 8#64), ProofLib.memRegion_eight (a + 16#64),
    ProofLib.memRegion_eight (a + 24#64), ProofLib.memRegion_eight (a + 32#64),
    ProofLib.memRegion_eight (a + 40#64), ProofLib.memRegion_eight (a + 48#64),
    ProofLib.memRegion_eight (a + 56#64), ProofLib.memRegion_eight (a + 64#64),
    ProofLib.memRegion_eight (a + 72#64), ProofLib.memRegion_eight (a + 120#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private noncomputable def e2b310_DomSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps cumCap maxReq : Nat) :
    Spec (ChunkedEkReceivedCt1SampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedEkReceivedCt1SampledDom x⌝ ∗
      (chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
        (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq)
        (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq)).pre (x, st) s
  post := (chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
    (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq)
    (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq)).post

private def e2b310_tightPoolAt {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (ops cum req : Nat) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜SpqrTightEvs ops cum req evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem e2b310_tightPoolAt_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {ops cum req : Nat} {s1 s2 : State}
    (hvm : VmPreserved s1 s2) :
    e2b310_tightPoolAt A lim st ops cum req s1 = e2b310_tightPoolAt A lim st ops cum req s2 := by
  unfold e2b310_tightPoolAt
  congr 1; funext evs
  rw [A.pool_of_vmPreserved hvm]

private theorem e2b310_pool_entails_tightPoolAt_init {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ e2b310_tightPoolAt A lim st 0 0 0 s :=
  Entails.sepExists_right [] (Entails.pure_right (SpqrTightEvs.nil 0 0 0) (Entails.refl _))

private theorem e2b310_tightPoolAt_mono {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {o1 o2 c1 c2 r1 r2 : Nat} {s : State}
    (ho : o1 ≤ o2) (hc : c1 ≤ c2) (hr : r1 ≤ r2) :
    e2b310_tightPoolAt A lim st o1 c1 r1 s ⊢ e2b310_tightPoolAt A lim st o2 c2 r2 s := by
  refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
  exact sepConj_mono_left (Entails.pure_mono fun h => h.mono ho hc hr)

private theorem e2b310_pool_entails_tightPoolAt_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {ops cum req : Nat}
    {evs evs_dv : List AllocEvent}
    (hevs : SpqrTightEvs ops cum req evs) (hnil : evs_dv = []) :
    A.pool lim (M.stepEvents evs_dv (M.stepEvents evs st)) s ⊢
      e2b310_tightPoolAt A lim st ops cum req s := by
  subst hnil
  unfold e2b310_tightPoolAt
  simpa only [AllocCostModel.stepEvents, List.foldl_nil] using
    (Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _)))

private theorem e2b310_pool_entails_tightPoolAt_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    {o1 c1 r1 o2 c2 r2 o3 c3 r3 : Nat} {evs1 evs2 : List AllocEvent}
    (ho : o1 + o2 ≤ o3) (hc : c1 + c2 ≤ c3) (hr : max r1 r2 ≤ r3)
    (h1 : SpqrTightEvs o1 c1 r1 evs1) (h2 : SpqrTightEvs o2 c2 r2 evs2) :
    A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s ⊢
      e2b310_tightPoolAt A lim st o3 c3 r3 s := by
  have hstep : M.stepEvents evs2 (M.stepEvents evs1 st) = M.stepEvents (evs1 ++ evs2) st := by
    simp only [AllocCostModel.stepEvents, List.foldl_append]
  rw [hstep]
  exact Entails.sepExists_right (evs1 ++ evs2)
    (Entails.pure_right ((h1.append h2).mono ho hc hr) (Entails.refl _))

private def e2b310_loopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.EkReceivedCt1Sampled) (bs cur : List (BitVec 8))
    (ops cum req : Nat) : SepProp :=
  e2b310_tightPoolAt A lim st ops cum req s ∗
    chunkedEkReceivedCt1SampledPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

private def e2b310_ucSeqPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (ucHeap : SepProp) (sendingCt1 : Option PolynomialEncoder)
    (bs cur : List (BitVec 8)) (ops cum req : Nat) : SepProp :=
  e2b310_tightPoolAt A lim st ops cum req s ∗
    ucHeap ∗
    optPolynomialEncoderPBAt A.repAlloc (msgPtr + 128#64) sendingCt1 ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

private theorem e2b310_fitsEnv_step {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps cumCap maxReq o1 c1 r1 : Nat} {evs1 : List AllocEvent} {P : List AllocEvent → Prop}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (_h1 : SpqrTightEvs o1 c1 r1 evs1)
    (himp : ∀ evs2, P evs2 → SpqrTightEvs maxOps cumCap maxReq (evs1 ++ evs2)) :
    FitsEnv M lim (M.stepEvents evs1 st) P :=
  fun evs2 hp =>
    ((fitsEvents_append M lim evs1 evs2 st).mp (hFit (evs1 ++ evs2) (himp evs2 hp))).2

private theorem e2b310_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps cumCap maxReq ops cum req : Nat} {cur : Bytes} {p : BitVec 64 × Bytes} {evs : List AllocEvent}
    (ho : ops ≤ maxOps) (hc : cum ≤ cumCap) (hr : req ≤ maxReq)
    (hd : decodeVarint cur = some p)
    (hevs : SpqrTightEvs ops cum req evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs st) (DecodeVarint2Env cur) :=
  e2b310_fitsEnv_step hFit hevs fun evs2 hdv => by
    rw [decodeVarint2Env_eq_nil_of_some hd hdv, List.append_nil]
    exact hevs.mono ho hc hr

private theorem e2b310_rustAllocEvents_tight {sz : Nat} (hsz : sz ≤ 2080) :
    SpqrTightEvs 1 9789 2080 (rustAllocEvents sz 1) :=
  (SpqrTightEvs.rustAlloc hsz (by decide : 1 ≤ 16)).mono (Nat.le_refl 1) (by decide) (Nat.le_refl 2080)

private theorem e2b310_rustDeallocEvents_tight (sz : Nat) :
    SpqrTightEvs 0 0 0 (rustDeallocEvents sz 1) :=
  SpqrTightEvs.rustDealloc sz 1

private theorem e2b310_bytesMerge3_tight_of_zeroCap
    {bs v rest' : Bytes} {evs : List AllocEvent}
    (hmb : mergeBytes .lengthDelimited bs = some (v, rest'))
    (hv : v.length ≤ 2080)
    (hevs : BytesMerge3EnvCore .lengthDelimited 0#64 bs evs) :
    SpqrTightEvs 2 19578 2080 evs := by
  change evs = bytesMergeEventsCore .lengthDelimited 0#64 bs at hevs
  rw [hevs]
  unfold bytesMergeEventsCore
  rw [hmb]
  dsimp only []
  split_ifs with h0
  · exact SpqrTightEvs.nil 2 19578 2080
  · have hpos : ¬ v.length ≤ 0 := by omega
    have hres_le : reserveCap 0 0 v.length ≤ 2080 := by dsimp [reserveCap]; omega
    have hdr : doReserveClearEvents (0#64 : BitVec 64).toNat v.length =
        rustAllocEvents (reserveCap 0 0 v.length) 1 := by
      unfold doReserveClearEvents
      simp only [BitVec.toNat_zero, hpos, ↓reduceIte]
    rw [hdr]
    have h1 := e2b310_rustAllocEvents_tight hv
    have h2 := e2b310_rustAllocEvents_tight hres_le
    have h3 := e2b310_rustDeallocEvents_tight v.length
    exact ((h1.append h2).append h3).mono (by decide) (by decide) (by decide)

private theorem e2b310_fitsEnv_bytesTight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps cumCap maxReq o1 c1 r1 : Nat}
    {x_bm : BytesMergeGhost} {v rest' : Bytes} {evs : List AllocEvent}
    (hwt : x_bm.wt = .lengthDelimited) (hcap : x_bm.valCap = 0#64)
    (hmb : mergeBytes .lengthDelimited x_bm.bs = some (v, rest'))
    (hv : v.length ≤ 2080)
    (ho : o1 + 2 ≤ maxOps) (hc : c1 + 19578 ≤ cumCap) (hr : max r1 2080 ≤ maxReq)
    (hevs : SpqrTightEvs o1 c1 r1 evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs st) (BytesMerge3Env x_bm) :=
  e2b310_fitsEnv_step hFit hevs fun evs2 hb => by
    unfold BytesMerge3Env at hb
    rw [hwt, hcap] at hb
    exact (hevs.append (e2b310_bytesMerge3_tight_of_zeroCap hmb hv hb)).mono ho hc hr

private theorem e2b310_fitsEnv_authTight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps authCum authReq maxOps cumCap maxReq : Nat}
    {x_auth : AuthMergeGhost} {evs : List AllocEvent}
    (hAuthDom : tlb_AuthDom x_auth)
    (ho : authOps ≤ maxOps) (hc : authCum ≤ cumCap) (hr : authReq ≤ maxReq)
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs st)
      (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv x_auth) :=
  tlb_fitsEnv_guarded_of_dom hAuthDom <|
    e2b310_fitsEnv_step hFit hevs fun _evs2 h2 =>
      (hevs.append h2).mono (by omega) (by omega) (by omega)

private theorem e2b310_fitsEnv_polyTight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {o1 c1 r1 encOps encCum encReq maxOps cumCap maxReq : Nat}
    {x_poly : PolyEncoderMergeGhost} {evs : List AllocEvent}
    (hPolyDom : tlb_PolyEncoderDom x_poly)
    (ho : o1 + encOps ≤ maxOps) (hc : c1 + encCum ≤ cumCap) (hr : max r1 encReq ≤ maxReq)
    (hevs : SpqrTightEvs o1 c1 r1 evs)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs st)
      (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv x_poly) :=
  tlb_fitsEnv_guarded_of_dom hPolyDom <|
    e2b310_fitsEnv_step hFit hevs fun _evs2 h2 =>
      (hevs.append h2).mono ho hc hr

private theorem e2b310_decodeVarint_encodeVarint (v : BitVec 64) (rest : Bytes) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ rest) =
      some (v, rest) := by
  rw [← proto_decodeVarint_toOption, proto_decodeVarint_encodeVarint]
  rfl

private theorem e2b310_mergeBytes_lenPrefixed (v after : Bytes) (hv : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (tlb_lenPrefixed v after) = some (v, after) := by
  unfold mergeBytes tlb_lenPrefixed
  rw [List.append_assoc, e2b310_decodeVarint_encodeVarint]
  have hlen : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have hnlt : ¬ (v ++ after).length < (BitVec.ofNat 64 v.length).toNat := by
    rw [hlen, List.length_append]; omega
  simp [hlen, hnlt, List.take_left, List.drop_left]

private theorem e2b310_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b310_vecU8ZeroCapAt_entails_capEk (A : RustAlloc) (a : BitVec 64)
    (n : Nat) (bs : List (BitVec 8)) :
    tlb_vecU8ZeroCapAt A a bs ⊢ vecU8CapAtEk A a n bs :=
  Entails.sepExists_elim fun ptr =>
    vecU8At_entails_vecU8CapAtEk A a 0#64 ptr n bs bytesMergeCapOk_zero

private theorem e2b310_default_cells_entails_authZeroCap (A : RustAlloc) (a : BitVec 64) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ⊢
      tlb_authenticatorZeroCapAt A a (default : ProtoAuthenticator) := by
  unfold tlb_authenticatorZeroCapAt
  have h1 := e2b310_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b310_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 0x18#64) 1#64 (by decide)
  simp only [arm64_norm] at h2
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

private theorem e2b310_default_cells_entails_polyEncoderZeroCap (A : RustAlloc) (p : BitVec 64) :
    ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4) ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt protoPolynomialEncoderPolysOff polyEncoderToProto
  have hvec : ∀ q : BitVec 64,
      (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 8#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢
        CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ q [] := fun q => by
    unfold CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt vecAt vecHeader vecBuf
    have hc0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hc0, ↓reduceIte, sepConj_emp]
    refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
    have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0 :=
      ⟨by decide, by decide, by decide⟩
    exact Entails.pure_right hp (Entails.refl _)
  have h1 := hvec p
  have h2 := hvec (p + 24#64)
  simp only [arm64_norm] at h2 ⊢
  change _ ⊢ CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + 24#64) [] ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  refine Entails.trans (Entails.of_eq (show
    ((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4) =
    (((p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64)) ∗
      (((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64)) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2b310_default_cells_entails_ucInitZeroCap (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 80#64) 40 ∗
      ((a + 120#64) ↦₆₄ 0#64)) ⊢
      (tlb_vecU8ZeroCapAt A a [] ∗
        tlb_vecU8ZeroCapAt A (a + 0x18#64) [] ∗
        tlb_vecU8ZeroCapAt A (a + 0x30#64) [] ∗
        optAuthenticatorPBCapAt A (a + 0x48#64) n none ∗
        ((a + 0x78#64) ↦₆₄ 0#64)) := by
  dsimp only [optAuthenticatorPBCapAt, noneCap]
  have h1 := e2b310_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b310_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 0x18#64) 1#64 (by decide)
  have h3 := e2b310_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 0x30#64) 1#64 (by decide)
  simp only [arm64_norm] at h2 h3 ⊢
  refine Entails.trans (Entails.of_eq (show
    ((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64) ∗
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 80#64) 40 ∗
      ((a + 120#64) ↦₆₄ 0#64)) =
    (((a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗
      (((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64)) ∗
      (((a + 48#64) ↦₆₄ 0#64) ∗ ((a + 56#64) ↦₆₄ 1#64) ∗ ((a + 64#64) ↦₆₄ 0#64)) ∗
      ((a + 72#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 80#64) 40 ∗
      ((a + 120#64) ↦₆₄ 0#64)) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3 (Entails.refl _)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option quotPrecheck false in
local notation "entry" => (blkPl_310).base

private theorem e2b310_uc_decode_known_key_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq ops cum req : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucHeap : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder}
    {cur rest : Bytes} {key : BitVec 64} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : ops ≤ maxOps) (hc : cum ≤ cumCap) (hr : req ≤ maxReq)
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 456#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr ucHeap sendingCt1 x.bs rest ops cum req)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr ucHeap sendingCt1 x.bs cur ops cum req)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 424#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, e2b310_stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (e2b310_fitsEnv_decodeVarint2_of_some ho hc hr hd hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 456#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b310_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2b310_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr ucHeap sendingCt1 x.bs rest ops cum req)
        (by dsimp only [e2b310_ucSeqPre]; rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
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

private theorem e2b310_uc_epoch_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucRest : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder} {epoch : BitVec 64}
    {afterEpoch : Bytes} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch))
    (hafter_gt : innerLimit ≤ afterEpoch.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (ucRest ∗ ((x.msgPtr + 0x78#64) ↦₆₄ epoch)) sendingCt1 x.bs afterEpoch 0 0 0)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (ucRest ∗ ((x.msgPtr + 0x78#64) ↦₆₄ 0#64)) sendingCt1
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch) 0 0 0)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  by_cases hep : epoch = 0#64
  · subst hep
    simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field, beq_self_eq_true,
      ↓reduceIte, List.nil_append] using
      hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hk8 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [8#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch =
        8#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch := by
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field,
        beq_iff_eq, hep, ↓reduceIte, hk8, List.singleton_append]
    have hgt : ¬ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length ≤ innerLimit := by
      rw [henc, List.cons_append, List.length_cons, List.length_append]; omega
    let rest1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint epoch ++ afterEpoch
    have hd_key : decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch) =
        some (8#64, rest1) := by
      rw [henc, List.cons_append]; rfl
    have hcur_lt : (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length < 2 ^ 63 :=
      Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_uc_decode_known_key_placed (iwt := .varint) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hrest1_le_cur : rest1.length ≤ (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 epoch ++ afterEpoch).length :=
      Nat.le_of_lt (decodeVarint_length hd_key)
    have hrest1_le : rest1.length ≤ x.bs.length := Nat.le_trans hrest1_le_cur hcur_le
    have hrest1_lt : rest1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le hbs_lt
    have hrest1_suf : IsDropSuffix x.bs rest1 :=
      suffix_trans hcur_le hcur_suf hrest1_le_cur (decodeVarint_suffix hd_key)
    let rest1Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest1.length)
    have hdv_ep : decodeVarint rest1 = some (epoch, afterEpoch) :=
      e2b310_decodeVarint_encodeVarint epoch afterEpoch
    have hafter_le_rest1 : afterEpoch.length ≤ rest1.length := Nat.le_of_lt (decodeVarint_length hdv_ep)
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt,
        sliceCursorAfter_eq_split hrest1_le hrest1_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, rest1Ptr, rest1⟩, M.stepEvents evs st))
        (ret_pc := entry + 620#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx19_1, e2b310_stackAt_decodeVarint2_raw_eq]; try rfl)
        (And.intro hrest1_lt (e2b310_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hdv_ep hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv_ep,
          e2b310_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest1_le hrest1_suf hafter_le_rest1) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hdv_ep hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            (ucRest ∗ ((x.msgPtr + 0x78#64) ↦₆₄ epoch)) sendingCt1 x.bs afterEpoch 0 0 0)
          (by dsimp only [e2b310_ucSeqPre];
              rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_uc_auth_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucRest : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder} {authOpt : Option ProtoAuthenticator}
    {afterAuth : Bytes} {outerLimit innerLimit outLen : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : authOps ≤ maxOps) (hc : authCum ≤ cumCap) (hr : authReq ≤ maxReq)
    (hValidAuthOpt : ∀ a, authOpt = some a → tlb_ValidAuthPB a)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 authOpt ++ afterAuth).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 authOpt ++ afterAuth))
    (hafter_gt : innerLimit ≤ afterAuth.length)
    (hout : outLen ≤ afterAuth.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (ucRest ∗ optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) outLen authOpt)
          sendingCt1 x.bs afterAuth authOps authCum authReq)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (ucRest ∗ optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) outLen none) sendingCt1
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          ProtoAuthenticator.encodeRaw 2#32 authOpt ++ afterAuth) 0 0 0)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  rcases authOpt with _ | authPb
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_ucSeqPre]; exact sepConj_mono_left (e2b310_tightPoolAt_mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs)
  · have hValidAuth : tlb_ValidAuthPB authPb := hValidAuthOpt authPb rfl
    let authPayload := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw authPb) afterAuth
    have hk18 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 (some authPb) ++ afterAuth = [18#8] ++ authPayload := by
      dsimp only [authPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk18, List.append_assoc]
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([18#8] ++ authPayload).length ≤ innerLimit := by
      simp only [List.singleton_append, List.length_cons, authPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([18#8] ++ authPayload) = some (18#64, authPayload) := rfl
    have hcur_lt : ([18#8] ++ authPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_uc_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : authPayload.length ≤ ([18#8] ++ authPayload).length := by simp
    have hpay_le : authPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : authPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs authPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - authPayload.length)
    let x_auth : AuthMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 0x48#64, default, x.bufRef, x.slot, payPtr, authPayload⟩
    have hAuthDom : tlb_AuthDom x_auth := ⟨rfl, rfl, authPb, afterAuth, hValidAuth, rfl⟩
    have hlenAuth : (ProtoAuthenticator.encodeRaw authPb).length < 2 ^ 64 := by
      have : (ProtoAuthenticator.encodeRaw authPb).length ≤ authPayload.length := by
        simp [authPayload, tlb_lenPrefixed]; omega
      omega
    have hmergeAuth : (mergeMessage ProtoAuthenticator.mergeField
        (codecWireTypeToProto .lengthDelimited) default authPayload 97).toOption =
        some (authPb, afterAuth) := by
      have hm := mergeMessage_encode ProtoAuthenticator.mergeField 0 ProtoAuthenticator.encodeRaw
        default authPb 97 afterAuth (loopsTo_authenticator authPb hlenAuth) hlenAuth (by decide)
      simpa only [codecWireTypeToProto, authPayload, tlb_lenPrefixed, List.append_assoc, Except.toOption] using
        congrArg Except.toOption hm
    have hafter_le_pay : afterAuth.length ≤ authPayload.length := by
      simp [authPayload, tlb_lenPrefixed]; omega
    apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
    by_vm_steps
      (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt,
        optAuthenticatorPBCapAt, memRegion_40_cells (x.msgPtr + 0x48#64),
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_authMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4
      apply SepWP.exists_elim; intro w5
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      have hdef := e2b310_default_cells_entails_authZeroCap A.repAlloc (x.msgPtr + 0x48#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_auth, M.stepEvents evs st))
        (ret_pc := entry + 560#64) hAuthTight
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [tlb_authMergeTightSpecOfEnv, x_auth];
            rw [tlb_domHeap_of_dom hAuthDom];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx0_1, hx20_1, hx19_1, setWidth8_ofNat64_wt]; try rfl)
        (And.intro hpay_lt (e2b310_fitsEnv_authTight hAuthDom ho hc hr hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv,
          AuthMergePostEnv, x_auth, hmergeAuth,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_auth
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x48#64) (some authPb) hout) (by dsimp only [optAuthenticatorPBCapAt]; sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_append A lim st sm
            (o3 := authOps) (c3 := authCum) (r3 := authReq)
            (by omega) (by omega) (by omega) hevs
            (tlb_guardedEnv_tight_of_dom hAuthDom hevs_auth))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            (ucRest ∗ optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) outLen (some authPb))
            sendingCt1 x.bs afterAuth authOps authCum authReq)
          (by dsimp only [e2b310_ucSeqPre];
              rw [← e2b310_tightPoolAt_of_vmPreserved hvm2];
              simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_uc_es_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {o1 c1 r1 maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucRest : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder} {es afterEs : Bytes}
    {outerLimit innerLimit outLen : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : o1 + 2 ≤ maxOps) (hc : c1 + 19578 ≤ cumCap) (hr : max r1 2080 ≤ maxReq)
    (hes : es.length ≤ 2080)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 es ++ afterEs).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 es ++ afterEs))
    (hafter_gt : innerLimit ≤ afterEs.length)
    (hout : outLen ≤ afterEs.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (vecU8CapAtEk A.repAlloc x.msgPtr outLen es ∗ ucRest)
          sendingCt1 x.bs afterEs (o1 + 2) (c1 + 19578) (max r1 2080))
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗ ucRest) sendingCt1
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 es ++ afterEs) o1 c1 r1)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  rcases es with _ | ⟨b_hd, b_tl⟩
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, List.isEmpty_nil,
      ↓reduceIte, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_ucSeqPre];
            exact sepConj_mono (e2b310_tightPoolAt_mono (by omega) (by omega) (Nat.le_max_left _ _))
              (sepConj_mono_left (sepConj_mono_left (e2b310_vecU8ZeroCapAt_entails_capEk A.repAlloc x.msgPtr outLen []))))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs)
  · let v := b_hd :: b_tl
    let esPayload := tlb_lenPrefixed v afterEs
    have hk26 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited = [26#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 v ++ afterEs =
        [26#8] ++ esPayload := by
      dsimp only [v, esPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, hk26, List.append_assoc]
    change _ at hcur_le hcur_suf
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([26#8] ++ esPayload).length ≤ innerLimit := by
      simp only [List.singleton_append, List.length_cons, esPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([26#8] ++ esPayload) = some (26#64, esPayload) := rfl
    have hcur_lt : ([26#8] ++ esPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_uc_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : esPayload.length ≤ ([26#8] ++ esPayload).length := by simp
    have hpay_le : esPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : esPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs esPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - esPayload.length)
    have hmb : mergeBytes .lengthDelimited esPayload = some (v, afterEs) :=
      e2b310_mergeBytes_lenPrefixed v afterEs (by dsimp only [v]; omega)
    have hafter_le_pay : afterEs.length ≤ esPayload.length := mergeBytes_length hmb
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt, tlb_vecU8ZeroCapAt,
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro ptr1
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      let x_bm : BytesMergeGhost := ⟨.lengthDelimited, x.msgPtr, 0#64, ptr1, [], x.bufRef, x.slot, payPtr, esPayload⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 580#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hpay_lt, bytesMergeCapOk_zero,
          e2b310_fitsEnv_bytesTight rfl rfl hmb hes ho hc hr hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec, x_bm]; simp only [hmb])
        (conv => arg 4; rw [← e2b310_vecU8CapAtEk_unfold A.repAlloc x.msgPtr afterEs.length v])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold (vecU8CapAtEk_mono A.repAlloc x.msgPtr v hout) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_append A lim st sm
            (o3 := o1 + 2) (c3 := c1 + 19578) (r3 := max r1 2080)
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hevs
            (e2b310_bytesMerge3_tight_of_zeroCap hmb hes hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            (vecU8CapAtEk A.repAlloc x.msgPtr outLen v ∗ ucRest)
            sendingCt1 x.bs afterEs (o1 + 2) (c1 + 19578) (max r1 2080))
          (by dsimp only [e2b310_ucSeqPre]; rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_uc_ek_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {o1 c1 r1 maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucRest : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder} {ek afterEk : Bytes}
    {outerLimit innerLimit outLen : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : o1 + 2 ≤ maxOps) (hc : c1 + 19578 ≤ cumCap) (hr : max r1 2080 ≤ maxReq)
    (hek : ek.length ≤ 2080)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ek ++ afterEk).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ek ++ afterEk))
    (hafter_gt : innerLimit ≤ afterEk.length)
    (hout : outLen ≤ afterEk.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (vecU8CapAtEk A.repAlloc (x.msgPtr + 0x18#64) outLen ek ∗ ucRest)
          sendingCt1 x.bs afterEk (o1 + 2) (c1 + 19578) (max r1 2080))
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗ ucRest) sendingCt1
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ek ++ afterEk) o1 c1 r1)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  rcases ek with _ | ⟨b_hd, b_tl⟩
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, List.isEmpty_nil,
      ↓reduceIte, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_ucSeqPre];
            exact sepConj_mono (e2b310_tightPoolAt_mono (by omega) (by omega) (Nat.le_max_left _ _))
              (sepConj_mono_left (sepConj_mono_left (e2b310_vecU8ZeroCapAt_entails_capEk A.repAlloc (x.msgPtr + 0x18#64) outLen []))))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs)
  · let v := b_hd :: b_tl
    let ekPayload := tlb_lenPrefixed v afterEk
    have hk34 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 4#32 .lengthDelimited = [34#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 v ++ afterEk =
        [34#8] ++ ekPayload := by
      dsimp only [v, ekPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, hk34, List.append_assoc]
    change _ at hcur_le hcur_suf
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([34#8] ++ ekPayload).length ≤ innerLimit := by
      simp only [List.singleton_append, List.length_cons, ekPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([34#8] ++ ekPayload) = some (34#64, ekPayload) := rfl
    have hcur_lt : ([34#8] ++ ekPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_uc_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : ekPayload.length ≤ ([34#8] ++ ekPayload).length := by simp
    have hpay_le : ekPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : ekPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs ekPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - ekPayload.length)
    have hmb : mergeBytes .lengthDelimited ekPayload = some (v, afterEk) :=
      e2b310_mergeBytes_lenPrefixed v afterEk (by dsimp only [v]; omega)
    have hafter_le_pay : afterEk.length ≤ ekPayload.length := mergeBytes_length hmb
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt, tlb_vecU8ZeroCapAt,
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro ptr1
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      let x_bm : BytesMergeGhost := ⟨.lengthDelimited, x.msgPtr + 0x18#64, 0#64, ptr1, [], x.bufRef, x.slot, payPtr, ekPayload⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 600#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hpay_lt, bytesMergeCapOk_zero,
          e2b310_fitsEnv_bytesTight rfl rfl hmb hek ho hc hr hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec, x_bm]; simp only [hmb])
        (conv => arg 4; rw [← e2b310_vecU8CapAtEk_unfold A.repAlloc (x.msgPtr + 0x18#64) afterEk.length v])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold (vecU8CapAtEk_mono A.repAlloc (x.msgPtr + 0x18#64) v hout) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_append A lim st sm
            (o3 := o1 + 2) (c3 := c1 + 19578) (r3 := max r1 2080)
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hevs
            (e2b310_bytesMerge3_tight_of_zeroCap hmb hek hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            (vecU8CapAtEk A.repAlloc (x.msgPtr + 0x18#64) outLen v ∗ ucRest)
            sendingCt1 x.bs afterEk (o1 + 2) (c1 + 19578) (max r1 2080))
          (by dsimp only [e2b310_ucSeqPre]; rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_uc_ct1_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {o1 c1 r1 maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R ucRest : SepProp} {s0 s : State}
    {sendingCt1 : Option PolynomialEncoder} {ct1 afterCt1 : Bytes}
    {outerLimit innerLimit outLen : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : o1 + 2 ≤ maxOps) (hc : c1 + 19578 ≤ cumCap) (hr : max r1 2080 ≤ maxReq)
    (hct1 : ct1.length ≤ 2080)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ afterCt1).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ afterCt1))
    (hafter_gt : innerLimit ≤ afterCt1.length)
    (hout : outLen ≤ afterCt1.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 404#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_ucSeqPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          (vecU8CapAtEk A.repAlloc (x.msgPtr + 0x30#64) outLen ct1 ∗ ucRest)
          sendingCt1 x.bs afterCt1 (o1 + 2) (c1 + 19578) (max r1 2080))
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗ ucRest) sendingCt1
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ct1 ++ afterCt1) o1 c1 r1)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  rcases ct1 with _ | ⟨b_hd, b_tl⟩
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, List.isEmpty_nil,
      ↓reduceIte, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_ucSeqPre];
            exact sepConj_mono (e2b310_tightPoolAt_mono (by omega) (by omega) (Nat.le_max_left _ _))
              (sepConj_mono_left (sepConj_mono_left (e2b310_vecU8ZeroCapAt_entails_capEk A.repAlloc (x.msgPtr + 0x30#64) outLen []))))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs)
  · let v := b_hd :: b_tl
    let ct1Payload := tlb_lenPrefixed v afterCt1
    have hk42 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 5#32 .lengthDelimited = [42#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 v ++ afterCt1 =
        [42#8] ++ ct1Payload := by
      dsimp only [v, ct1Payload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, hk42, List.append_assoc]
    change _ at hcur_le hcur_suf
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([42#8] ++ ct1Payload).length ≤ innerLimit := by
      simp only [List.singleton_append, List.length_cons, ct1Payload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([42#8] ++ ct1Payload) = some (42#64, ct1Payload) := rfl
    have hcur_lt : ([42#8] ++ ct1Payload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_uc_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : ct1Payload.length ≤ ([42#8] ++ ct1Payload).length := by simp
    have hpay_le : ct1Payload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : ct1Payload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs ct1Payload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - ct1Payload.length)
    have hmb : mergeBytes .lengthDelimited ct1Payload = some (v, afterCt1) :=
      e2b310_mergeBytes_lenPrefixed v afterCt1 (by dsimp only [v]; omega)
    have hafter_le_pay : afterCt1.length ≤ ct1Payload.length := mergeBytes_length hmb
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [e2b310_ucSeqPre, e2b310_tightPoolAt, tlb_vecU8ZeroCapAt,
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro ptr1
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      let x_bm : BytesMergeGhost := ⟨.lengthDelimited, x.msgPtr + 0x30#64, 0#64, ptr1, [], x.bufRef, x.slot, payPtr, ct1Payload⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 500#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hpay_lt, bytesMergeCapOk_zero,
          e2b310_fitsEnv_bytesTight rfl rfl hmb hct1 ho hc hr hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; dsimp only [bytesMerge3RawBudgetSpec, x_bm]; simp only [hmb])
        (conv => arg 4; rw [← e2b310_vecU8CapAtEk_unfold A.repAlloc (x.msgPtr + 0x30#64) afterCt1.length v])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold (vecU8CapAtEk_mono A.repAlloc (x.msgPtr + 0x30#64) v hout) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_append A lim st sm
            (o3 := o1 + 2) (c3 := c1 + 19578) (r3 := max r1 2080)
            (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hevs
            (e2b310_bytesMerge3_tight_of_zeroCap hmb hct1 hevs_b))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            (vecU8CapAtEk A.repAlloc (x.msgPtr + 0x30#64) outLen v ∗ ucRest)
            sendingCt1 x.bs afterCt1 (o1 + 2) (c1 + 19578) (max r1 2080))
          (by dsimp only [e2b310_ucSeqPre]; rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_uc_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {ops cum req maxOps cumCap maxReq : Nat}
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucPb : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {afterUc : Bytes} {outerLimit : Nat}
    (hcur_le : afterUc.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs afterUc)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := some ucPb, sendingCt1 := sendingCt1 } x.bs afterUc ops cum req)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 afterUc.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_ucSeqPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        (vecU8CapAtEk A.repAlloc x.msgPtr afterUc.length ucPb.es ∗
          vecU8CapAtEk A.repAlloc (x.msgPtr + 0x18#64) afterUc.length ucPb.ek ∗
          vecU8CapAtEk A.repAlloc (x.msgPtr + 0x30#64) afterUc.length ucPb.ct1 ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length ucPb.auth ∗
          ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch))
        sendingCt1 x.bs afterUc ops cum req)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : afterUc.length = afterUc.length)
  apply sepWPpLscro_of_vm (mid := entry + 168#64)
  by_vm_steps
    (conv => arg 4; rw [e2b310_ucSeqPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    apply SepWPpLscro.weaken_pre
      (P' := e2b310_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { uc := some ucPb, sendingCt1 := sendingCt1 } x.bs afterUc ops cum req)
      (by dsimp only [e2b310_loopPre, chunkedEkReceivedCt1SampledPBCapAt,
            optCt1SentEkReceivedPBCapAt, sliceCursorAfter];
          rw [unchunked5CapAt_eq, ← e2b310_tightPoolAt_of_vmPreserved hvm];
          simp only [arm64_norm]; sep_entail)
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

private theorem e2b310_decode_known_key_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq ops cum req : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled}
    {cur rest : Bytes} {key : BitVec 64} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : ops ≤ maxOps) (hc : cum ≤ cumCap) (hr : req ≤ maxReq)
    (hgt_lim : ¬ cur.length ≤ outerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest ops cum req)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur ops cum req)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b310_loopPre, e2b310_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 188#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, e2b310_stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (e2b310_fitsEnv_decodeVarint2_of_some ho hc hr hd hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 228#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b310_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2b310_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := e2b310_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest ops cum req)
        (by dsimp only [e2b310_loopPre]; rw [← e2b310_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
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

private theorem e2b310_tag1_uc_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.Ct1SentEkReceived}
    {afterUc : Bytes} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : authOps + 6 ≤ maxOps) (hc : authCum + 58734 ≤ cumCap) (hr : max authReq 2080 ≤ maxReq)
    (hValidUcOpt : ∀ u, ucOpt = some u → tlb_ValidUcCt1SentEkReceivedPB u)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 ucOpt ++ afterUc).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 ucOpt ++ afterUc))
    (hafter_gt : outerLimit ≤ afterUc.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, sendingCt1 := none } x.bs afterUc
          (authOps + 6) (authCum + 58734) (max authReq 2080))
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr default
        x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 ucOpt ++ afterUc) 0 0 0)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  rcases ucOpt with _ | ucPb
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_loopPre]; exact sepConj_mono_left (e2b310_tightPoolAt_mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs)
  · obtain ⟨hValidAuthOpt, hes_le, hek_le, hct1_le⟩ := hValidUcOpt ucPb rfl
    let rawUc := V1State.Unchunked.Ct1SentEkReceived.encodeRaw ucPb
    let ucPayload := tlb_lenPrefixed rawUc afterUc
    have hk10 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited = [10#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 (some ucPb) ++ afterUc =
        [10#8] ++ ucPayload := by
      dsimp only [rawUc, ucPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk10, List.append_assoc]
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([10#8] ++ ucPayload).length ≤ outerLimit := by
      simp only [List.singleton_append, List.length_cons, ucPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([10#8] ++ ucPayload) = some (10#64, ucPayload) := rfl
    have hcur_lt : ([10#8] ++ ucPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : ucPayload.length ≤ ([10#8] ++ ucPayload).length := by simp
    have hpay_le : ucPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt : ucPayload.length < 2 ^ 63 := Nat.lt_of_le_of_lt hpay_le hbs_lt
    have hpay_suf : IsDropSuffix x.bs ucPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - ucPayload.length)
    let rest0 := rawUc ++ afterUc
    have hdv_uc : decodeVarint ucPayload = some (BitVec.ofNat 64 rawUc.length, rest0) := by
      dsimp only [ucPayload, tlb_lenPrefixed, rest0]
      rw [List.append_assoc]
      exact e2b310_decodeVarint_encodeVarint (BitVec.ofNat 64 rawUc.length) rest0
    have hrest0_le_pay : rest0.length ≤ ucPayload.length := Nat.le_of_lt (decodeVarint_length hdv_uc)
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_pay hpay_le
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs rest0 :=
      suffix_trans hpay_le hpay_suf hrest0_le_pay (decodeVarint_suffix hdv_uc)
    have hraw_lt : rawUc.length < 2 ^ 64 := by
      have : rawUc.length ≤ rest0.length := by simp [rest0]
      omega
    have hlen_raw : (BitVec.ofNat 64 rawUc.length).toNat = rawUc.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt]
    have hge_len : ¬ rest0.length < (BitVec.ofNat 64 rawUc.length).toNat := by
      rw [hlen_raw]; simp [rest0]
    have hule := ule_len_of_ge hge_len hrest0_lt
    have hult : (BitVec.ofNat 64 rest0.length).ult (BitVec.ofNat 64 rawUc.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : rest0.length < 2 ^ 64),
        Nat.mod_eq_of_lt hraw_lt, decide_eq_false_iff_not]
      omega
    have hsub := bv_len_sub_limit hge_len
    have hlim_eq : rest0.length - (BitVec.ofNat 64 rawUc.length).toNat = afterUc.length := by
      rw [hlen_raw]; simp [rest0]
    have hlim_eq' : rest0.length - rawUc.length = afterUc.length := by simp [rest0]
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b310_loopPre, e2b310_tightPoolAt, chunkedEkReceivedCt1SampledPBCapAt,
        show (default : V1State.Chunked.EkReceivedCt1Sampled).uc = none from rfl,
        optCt1SentEkReceivedPBCapAt, e2b310_memRegion_unchunked5_none_split x.msgPtr,
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro v120; apply SepWP.exists_elim; intro v72
      apply SepWP.exists_elim; intro v64; apply SepWP.exists_elim; intro v56
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
      apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (e2b310_default_cells_entails_ucInitZeroCap A.repAlloc x.msgPtr afterUc.length) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, payPtr, ucPayload⟩, M.stepEvents evs st))
        (ret_pc := entry + 352#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
            simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1, hx19_1, e2b310_stackAt_decodeVarint2_raw_eq]; try rfl)
        (And.intro hpay_lt (e2b310_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hdv_uc hevs hFit))
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 404#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv_uc,
          e2b310_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hrest0_le_pay) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_nil A lim st sm hevs (decodeVarint2Env_eq_nil_of_some hdv_uc hevs_dv))
          (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        let afterEpoch := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ucPb.es ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ucPb.ek ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ucPb.ct1 ++ afterUc
        let afterAuth := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ucPb.es ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ucPb.ek ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ucPb.ct1 ++ afterUc
        let afterEs := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ucPb.ek ++
          CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ucPb.ct1 ++ afterUc
        let afterEk := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ucPb.ct1 ++ afterUc
        have hrest0_eq : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch := by
          dsimp only [rest0, rawUc, V1State.Unchunked.Ct1SentEkReceived.encodeRaw, afterEpoch]
          simp only [List.append_assoc]
        have hafterEpoch_eq : afterEpoch = CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterAuth := by
          dsimp only [afterEpoch, afterAuth]; simp only [List.append_assoc]
        have hafterAuth_eq : afterAuth = CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ucPb.es ++ afterEs := by
          dsimp only [afterAuth, afterEs]; simp only [List.append_assoc]
        have hafterEs_eq : afterEs = CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ucPb.ek ++ afterEk := by
          dsimp only [afterEs, afterEk]; simp only [List.append_assoc]
        have hep_le_r0 : afterEpoch.length ≤ rest0.length := by rw [hrest0_eq]; simp
        have hau_le_ep : afterAuth.length ≤ afterEpoch.length := by rw [hafterEpoch_eq]; simp
        have hes_le_au : afterEs.length ≤ afterAuth.length := by rw [hafterAuth_eq]; simp
        have hek_le_es : afterEk.length ≤ afterEs.length := by rw [hafterEs_eq]; simp
        have huc_le_ek : afterUc.length ≤ afterEk.length := by dsimp only [afterEk]; simp
        have hep_le : afterEpoch.length ≤ x.bs.length := Nat.le_trans hep_le_r0 hrest0_le
        have hau_le : afterAuth.length ≤ x.bs.length := Nat.le_trans hau_le_ep hep_le
        have hafterEs_le : afterEs.length ≤ x.bs.length := Nat.le_trans hes_le_au hau_le
        have hafterEk_le : afterEk.length ≤ x.bs.length := Nat.le_trans hek_le_es hafterEs_le
        have hafterUc_le : afterUc.length ≤ x.bs.length := Nat.le_trans huc_le_ek hafterEk_le
        have hep_suf : IsDropSuffix x.bs afterEpoch := by
          have hs : IsDropSuffix rest0 afterEpoch := by
            rw [hrest0_eq]; unfold IsDropSuffix; simp [List.drop_left]
          exact suffix_trans hrest0_le hrest0_suf hep_le_r0 hs
        have hau_suf : IsDropSuffix x.bs afterAuth := by
          have hs : IsDropSuffix afterEpoch afterAuth := by
            rw [hafterEpoch_eq]; unfold IsDropSuffix; simp [List.drop_left]
          exact suffix_trans hep_le hep_suf hau_le_ep hs
        have hes_suf : IsDropSuffix x.bs afterEs := by
          have hs : IsDropSuffix afterAuth afterEs := by
            rw [hafterAuth_eq]; unfold IsDropSuffix; simp [List.drop_left]
          exact suffix_trans hau_le hau_suf hes_le_au hs
        have hek_suf : IsDropSuffix x.bs afterEk := by
          have hs : IsDropSuffix afterEs afterEk := by
            rw [hafterEs_eq]; unfold IsDropSuffix; simp [List.drop_left]
          exact suffix_trans hafterEs_le hes_suf hek_le_es hs
        have hafterUc_suf : IsDropSuffix x.bs afterUc := by
          have hs : IsDropSuffix afterEk afterUc := by
            dsimp only [afterEk]; unfold IsDropSuffix; simp [List.drop_left]
          exact suffix_trans hafterEk_le hek_suf huc_le_ek hs
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            ((tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length none) ∗
              ((x.msgPtr + 0x78#64) ↦₆₄ 0#64))
            none x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field 1#32 ucPb.epoch ++ afterEpoch) 0 0 0)
          (by dsimp only [e2b310_ucSeqPre, sliceCursorAfter];
              rw [← hrest0_eq, ← e2b310_tightPoolAt_of_vmPreserved hvm2];
              simp only [arm64_norm]; sep_entail)
        refine e2b310_uc_epoch_opt_step_placed (outerLimit := outerLimit) (innerLimit := afterUc.length) hVarintCall hFit
          hsp_align hbs_lt (by rw [← hrest0_eq]; exact hrest0_le) (by rw [← hrest0_eq]; exact hrest0_suf)
          (by omega) ?_
          (by simp only [arm64_norm, wp_norm, hult])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m])
          (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlim_eq, hlim_eq'])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        intro se hpce hrun_e hsp_e htr_e hx19_e hx20_e hx21_e hx22_e hx23_e hx24_e hx25_e hx26_e hcs_e
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 se x.msgPtr x.bufRef x.slot x.ptr
            ((tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
              ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch)) ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length none)
            none x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 ucPb.auth ++ afterAuth) 0 0 0)
          (by dsimp only [e2b310_ucSeqPre]; rw [← hafterEpoch_eq]; exact Entails.of_eq (by sep_ac_rfl))
        refine e2b310_uc_auth_opt_step_placed hVarintCall hAuthTight hFit
          (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr) hValidAuthOpt
          hsp_align hbs_lt (by rw [← hafterEpoch_eq]; exact hep_le) (by rw [← hafterEpoch_eq]; exact hep_suf)
          (by omega) (by omega) ?_
          hpce hrun_e hsp_e htr_e hx19_e hx20_e hx21_e hx22_e hx23_e hx24_e hx25_e hx26_e hcs_e
        intro sa hpca hrun_a hsp_a htr_a hx19_a hx20_a hx21_a hx22_a hx23_a hx24_a hx25_a hx26_a hcs_a
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 sa x.msgPtr x.bufRef x.slot x.ptr
            (tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
              (tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
                tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
                optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length ucPb.auth ∗
                ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch)))
            none x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 ucPb.es ++ afterEs)
            authOps authCum authReq)
          (by dsimp only [e2b310_ucSeqPre]; rw [← hafterAuth_eq]; exact Entails.of_eq (by sep_ac_rfl))
        refine e2b310_uc_es_opt_step_placed (outLen := afterUc.length) hVarintCall hBytesCall hFit
          (by omega) (by omega) hr hes_le
          hsp_align hbs_lt (by rw [← hafterAuth_eq]; exact hau_le) (by rw [← hafterAuth_eq]; exact hau_suf)
          (by omega) (by omega) ?_
          hpca hrun_a hsp_a htr_a hx19_a hx20_a hx21_a hx22_a hx23_a hx24_a hx25_a hx26_a hcs_a
        intro ss hpcs hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s hx25_s hx26_s hcs_s
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 ss x.msgPtr x.bufRef x.slot x.ptr
            (tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) [] ∗
              (vecU8CapAtEk A.repAlloc x.msgPtr afterUc.length ucPb.es ∗
                tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
                optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length ucPb.auth ∗
                ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch)))
            none x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 4#32 ucPb.ek ++ afterEk)
            (authOps + 2) (authCum + 19578) (max authReq 2080))
          (by dsimp only [e2b310_ucSeqPre]; rw [← hafterEs_eq]; exact Entails.of_eq (by sep_ac_rfl))
        refine e2b310_uc_ek_opt_step_placed (outLen := afterUc.length) hVarintCall hBytesCall hFit
          (by omega) (by omega) (by rw [Nat.max_assoc, Nat.max_self]; exact hr) (by omega)
          hsp_align hbs_lt (by rw [← hafterEs_eq]; exact hafterEs_le) (by rw [← hafterEs_eq]; exact hes_suf)
          (by omega) (by omega) ?_
          hpcs hrun_s hsp_s htr_s hx19_s hx20_s hx21_s hx22_s hx23_s hx24_s hx25_s hx26_s hcs_s
        intro sk hpck hrun_k hsp_k htr_k hx19_k hx20_k hx21_k hx22_k hx23_k hx24_k hx25_k hx26_k hcs_k
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 sk x.msgPtr x.bufRef x.slot x.ptr
            (tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 0x30#64) [] ∗
              (vecU8CapAtEk A.repAlloc x.msgPtr afterUc.length ucPb.es ∗
                vecU8CapAtEk A.repAlloc (x.msgPtr + 0x18#64) afterUc.length ucPb.ek ∗
                optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length ucPb.auth ∗
                ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch)))
            none x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 5#32 ucPb.ct1 ++ afterUc)
            (authOps + 2 + 2) (authCum + 19578 + 19578) (max (max authReq 2080) 2080))
          (by dsimp only [e2b310_ucSeqPre, afterEk]; exact Entails.of_eq (by sep_ac_rfl))
        refine e2b310_uc_ct1_opt_step_placed (outLen := afterUc.length) hVarintCall hBytesCall hFit
          (by omega) (by omega) (by simp only [Nat.max_assoc, Nat.max_self]; exact hr) (by omega)
          hsp_align hbs_lt (by dsimp only [afterEk] at hafterEk_le; exact hafterEk_le)
          (by dsimp only [afterEk] at hek_suf; exact hek_suf)
          (Nat.le_refl _) (Nat.le_refl _) ?_
          hpck hrun_k hsp_k htr_k hx19_k hx20_k hx21_k hx22_k hx23_k hx24_k hx25_k hx26_k hcs_k
        intro sc hpcc hrun_c hsp_c htr_c hx19_c hx20_c hx21_c hx22_c hx23_c hx24_c hx25_c hx26_c hcs_c
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_ucSeqPre A lim st s0 sc x.msgPtr x.bufRef x.slot x.ptr
            (vecU8CapAtEk A.repAlloc x.msgPtr afterUc.length ucPb.es ∗
              vecU8CapAtEk A.repAlloc (x.msgPtr + 0x18#64) afterUc.length ucPb.ek ∗
              vecU8CapAtEk A.repAlloc (x.msgPtr + 0x30#64) afterUc.length ucPb.ct1 ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x48#64) afterUc.length ucPb.auth ∗
              ((x.msgPtr + 0x78#64) ↦₆₄ ucPb.epoch))
            none x.bs afterUc (authOps + 6) (authCum + 58734) (max authReq 2080))
          (by dsimp only [e2b310_ucSeqPre];
              refine sepConj_mono (e2b310_tightPoolAt_mono (by omega) (by omega) (by simp [Nat.max_assoc, Nat.max_self]))
                (Entails.of_eq (by sep_ac_rfl)))
        exact e2b310_uc_exit_placed hafterUc_le hafterUc_suf hcont
          hpcc hrun_c hsp_c htr_c hx19_c hx20_c hx21_c hx22_c hx23_c hx24_c hx25_c hx26_c hcs_c

private theorem e2b310_tag2_ct1_opt_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {o1 c1 r1 encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.Ct1SentEkReceived}
    {encOpt : Option PolynomialEncoder}
    {after0 : Bytes} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (ho : o1 + encOps ≤ maxOps) (hc : c1 + encCum ≤ cumCap) (hr : max r1 encReq ≤ maxReq)
    (hValidEncOpt : ∀ e, encOpt = some e → tlb_ValidPolyEncoderPB e)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialEncoder.encodeRaw 2#32 encOpt ++ after0).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialEncoder.encodeRaw 2#32 encOpt ++ after0))
    (hafter_gt : outerLimit ≤ after0.length)
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (e2b310_loopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, sendingCt1 := encOpt } x.bs after0 maxOps cumCap maxReq)
        (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_310).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        { uc := ucOpt, sendingCt1 := none } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          PolynomialEncoder.encodeRaw 2#32 encOpt ++ after0) o1 c1 r1)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  rcases encOpt with _ | encPb
  · simpa only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append] using
      SepWPpLscro.weaken_pre
        (by dsimp only [e2b310_loopPre]; exact sepConj_mono_left (e2b310_tightPoolAt_mono (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr)))
        (hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs)
  · have hValidEnc : tlb_ValidPolyEncoderPB encPb := hValidEncOpt encPb rfl
    let encPayload := tlb_lenPrefixed (PolynomialEncoder.encodeRaw encPb) after0
    have hk18 : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited = [18#8] := by decide
    have henc : CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 (some encPb) ++ after0 = [18#8] ++ encPayload := by
      dsimp only [encPayload, tlb_lenPrefixed]
      simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
        CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk18, List.append_assoc]
    rw [henc] at hcur_le hcur_suf ⊢
    have hgt : ¬ ([18#8] ++ encPayload).length ≤ outerLimit := by
      simp only [List.singleton_append, List.length_cons, encPayload, tlb_lenPrefixed, List.length_append]; omega
    have hd_key : decodeVarint ([18#8] ++ encPayload) = some (18#64, encPayload) := rfl
    have hcur_lt : ([18#8] ++ encPayload).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    refine e2b310_decode_known_key_placed (iwt := .lengthDelimited) hVarintCall hFit
      (by omega) (by omega) (Nat.le_trans (Nat.le_max_left _ _) hr)
      hgt hsp_align hcur_le hcur_lt hcur_suf hd_key (by decide) (by decide) (by decide) ?_
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hpay_le_cur : encPayload.length ≤ ([18#8] ++ encPayload).length := by simp
    have hpay_le : encPayload.length ≤ x.bs.length := Nat.le_trans hpay_le_cur hcur_le
    have hpay_lt56 : encPayload.length < 2 ^ 56 := Nat.lt_of_le_of_lt hpay_le hbs_lt56
    have hpay_suf : IsDropSuffix x.bs encPayload :=
      suffix_trans hcur_le hcur_suf hpay_le_cur (decodeVarint_suffix hd_key)
    let payPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - encPayload.length)
    let x_poly : PolyEncoderMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 128#64, default, x.bufRef, x.slot, payPtr, encPayload⟩
    have hPolyDom : tlb_PolyEncoderDom x_poly := ⟨rfl, rfl, encPb, after0, hValidEnc, rfl⟩
    have hlenEnc : (PolynomialEncoder.encodeRaw encPb).length < 2 ^ 64 := by
      have : (PolynomialEncoder.encodeRaw encPb).length ≤ encPayload.length := by
        simp [encPayload, tlb_lenPrefixed]; omega
      omega
    have hmergeEnc : (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto .lengthDelimited) default encPayload 98).toOption =
        some (encPb, after0) := by
      have hm := mergeMessage_encode PolynomialEncoder.mergeField 0 PolynomialEncoder.encodeRaw
        default encPb 98 after0 (loopsTo_polyEncoder encPb hlenEnc) hlenEnc (by decide)
      simpa only [codecWireTypeToProto, encPayload, tlb_lenPrefixed, List.append_assoc, Except.toOption] using
        congrArg Except.toOption hm
    have hafter_le_pay : after0.length ≤ encPayload.length := by
      simp [encPayload, tlb_lenPrefixed]; omega
    apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
    by_vm_steps
      (conv => arg 4; rw [e2b310_loopPre, e2b310_tightPoolAt, chunkedEkReceivedCt1SampledPBCapAt,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split_inl (x.msgPtr + 128#64),
        sliceCursorAfter_eq_split hpay_le hpay_suf, chunkedInlBelow_eq_polyMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
      apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      have hdef := e2b310_default_cells_entails_polyEncoderZeroCap A.repAlloc (x.msgPtr + 128#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
        (ret_pc := entry + 288#64) hPolyTight
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_polyEncoderMergeTightSpecOfEnv]
              rw [tlb_domHeap_of_dom hPolyDom]
              dsimp only [x_poly]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx8_1, e2b310_setWidth8_zext64_trunc32_ofNat64_wt],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          by change ([] : List Bytes).length + encPayload.length < 2 ^ 56; simpa using hpay_lt56,
          by change ([] : List Bytes).length + encPayload.length < 2 ^ 56; simpa using hpay_lt56,
          e2b310_fitsEnv_polyTight hPolyDom ho hc hr hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_poly, hmergeEnc, ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_p⟩, hsm0⟩
        apply SepWP.fold (sliceCursorAfter_join hpay_le hpay_suf hafter_le_pay) (by sep_focus)
        apply SepWP.fold (optCt1SentEkReceivedPBCapAt_mono A.repAlloc x.msgPtr ucOpt hafter_le_pay) (by sep_focus)
        apply SepWP.fold
          (e2b310_pool_entails_tightPoolAt_append A lim st sm
            (o3 := maxOps) (c3 := cumCap) (r3 := maxReq)
            ho hc hr hevs (tlb_guardedEnv_tight_of_dom hPolyDom hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := e2b310_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc := ucOpt, sendingCt1 := some encPb } x.bs after0 maxOps cumCap maxReq)
          (by dsimp only [e2b310_loopPre, chunkedEkReceivedCt1SampledPBCapAt];
              rw [optPolynomialEncoderPBAt_some_eq, ← e2b310_tightPoolAt_of_vmPreserved hvm2];
              simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
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

private theorem e2b310_dom_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps cumCap maxReq : Nat) (st : M.σ)
    (x : ChunkedEkReceivedCt1SampledMergeGhost) (s0 s sf : State)
    (ck : V1State.Chunked.EkReceivedCt1Sampled) (after0 : Bytes)
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedEkReceivedCt1SampledDom x)
    (hsome : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (ck, after0))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedEkReceivedCt1SampledPBCapAt A.repAlloc x.msgPtr after0.length ck ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs after0 ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2b310_DomSpec A lim maxOps cumCap maxReq).post (x, st) s0 sf := by
  dsimp only [e2b310_DomSpec, chunkedEkReceivedCt1SampledMergeSpecOfEnv]
  rw [hsome, htr, hx0, ← A.pool_of_vmPreserved hvm]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedEkReceivedCt1SampledPBCapAt A.repAlloc x.msgPtr after0.length ck ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs after0 ∗ A.pool lim (M.stepEvents evs st) sf))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) sf ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedEkReceivedCt1SampledPBCapAt A.repAlloc x.msgPtr after0.length ck ∗
            sliceCursorAfter x.slot x.ptr x.bs after0))))) ?_
  have hguard : e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq x evs :=
    Or.inl ⟨hDom, hevs⟩
  exact sepConj_mono_right (sepConj_mono
    (Entails.sepExists_right evs (Entails.pure_right hguard (Entails.refl _)))
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2b310_outer_exit_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ck : V1State.Chunked.EkReceivedCt1Sampled} {after0 : Bytes}
    (hDom : tlb_ChunkedEkReceivedCt1SampledDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsome : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (ck, after0))
    (hcur_le : after0.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs after0)
    (hpc : s.pc = (blkPl_310).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 after0.length)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (_hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (e2b310_loopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr ck x.bs after0 maxOps cumCap maxReq)
      (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : after0.length = after0.length)
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - after0.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b310_loopPre, e2b310_tightPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlSavedRegs10,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    have hcur_fold :
        (x.slot ↦₆₄ curPtr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 after0.length) ∗
          (x.ptr ↦ₛ x.bs.take (x.bs.length - after0.length)) ∗ (curPtr ↦ₛ after0) ⊢
        sliceCursorAfter x.slot x.ptr x.bs after0 := by
      rw [sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt]
      dsimp only [curPtr]
      exact Entails.of_eq (by sep_ac_rfl)
    apply SepWP.fold hcur_fold (by dsimp only [curPtr]; sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    refine ⟨fun hm => Satisfies.of_entails hm (sepConj_mono_left ?_),
      by simp only [arm64_norm, wp_norm, hsp],
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2b310_dom_ok_exit_entails A lim maxOps cumCap maxReq st x s0 s _ ck after0 evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b310_dom_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + e2b310_ownBytesOps + encOps ≤ maxOps)
    (hCum : authCum + e2b310_ownBytesCum + encCum ≤ cumCap)
    (hReq : max e2b310_ownBytesMaxReq (max authReq encReq) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    (hPolyTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)))) :
    subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (blkPl_310).base
      (withLsCodeRoLoaded lsmpl (e2b310_DomSpec A lim maxOps cumCap maxReq)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b310_DomSpec chunkedEkReceivedCt1SampledMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only []
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b310_DomSpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim; intro hDom
  apply sepWPpLscro_pure_elim; rintro ⟨h_1, h_2, h_3, hbound, hFit_dom⟩
  have hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq) :=
    fun evs hevs => hFit_dom evs (Or.inl ⟨hDom, hevs⟩)
  have ⟨hWt_proto, hMsg, ck, after0, ⟨hValidUcOpt, hValidEncOpt⟩, hBs⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := by
    cases hwt : x.wt <;> simp [hwt, codecWireTypeToProto] at hWt_proto; rfl
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by
    rw [hMsg] at hbound; unfold OptPolyEncoderBound at hbound
    exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hbound.1
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  let rawCk := V1State.Chunked.EkReceivedCt1Sampled.encodeRaw ck
  let rest0 := rawCk ++ after0
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 rawCk.length, rest0) := by
    rw [hBs]; dsimp only [rawCk, rest0, tlb_lenPrefixed]
    rw [List.append_assoc]
    exact e2b310_decodeVarint_encodeVarint (BitVec.ofNat 64 rawCk.length) rest0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hrawCk_lt : rawCk.length < 2 ^ 64 := by
    have : rawCk.length ≤ rest0.length := by simp [rest0]
    omega
  have hlen_rawCk : (BitVec.ofNat 64 rawCk.length).toNat = rawCk.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrawCk_lt]
  have hge_len0 : ¬ rest0.length < (BitVec.ofNat 64 rawCk.length).toNat := by
    rw [hlen_rawCk]; simp [rest0]
  have hule0 := ule_len_of_ge hge_len0 hrest0_lt
  have hsub0 := bv_len_sub_limit hge_len0
  have hlim0_eq : rest0.length - (BitVec.ofNat 64 rawCk.length).toNat = after0.length := by
    rw [hlen_rawCk]; simp [rest0]
  have hlim0_eq' : rest0.length - rawCk.length = after0.length := by simp [rest0]
  have hmergeCk : (mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (ck, after0) := by
    rw [hWt_proto, hMsg, hBs]
    have hm := mergeMessage_encode V1State.Chunked.EkReceivedCt1Sampled.mergeField 2
      V1State.Chunked.EkReceivedCt1Sampled.encodeRaw default ck 99 after0
      (loopsTo_ch_ekReceivedCt1Sampled ck hrawCk_lt) hrawCk_lt (by decide)
    simpa only [tlb_lenPrefixed, List.append_assoc, Except.toOption] using
      congrArg Except.toOption hm
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
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
            simp only [A.pool_of_vmPreserved hvm1, e2b310_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3],
        hbs_lt,
        by simpa only [AllocCostModel.stepEvents, List.foldl_nil] using
             e2b310_fitsEnv_decodeVarint2_of_some (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
               hdv0 (SpqrTightEvs.nil 0 0 0) hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b310_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
      have hpool0 : A.pool lim (M.stepEvents evs_dv st) sm ⊢ e2b310_tightPoolAt A lim st 0 0 0 sm := by
        rw [decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv]
        simpa only [AllocCostModel.stepEvents, List.foldl] using
          e2b310_pool_entails_tightPoolAt_init A lim st sm
      apply SepWP.fold hpool0 (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      let afterUc := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 ck.sendingCt1 ++ after0
      have hrest0_eq : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 ck.uc ++ afterUc := by
        dsimp only [rest0, rawCk, V1State.Chunked.EkReceivedCt1Sampled.encodeRaw, afterUc]
        simp only [List.append_assoc]
      have hafterUc_le_r0 : afterUc.length ≤ rest0.length := by rw [hrest0_eq]; simp
      have hafterUc_le : afterUc.length ≤ x.bs.length := Nat.le_trans hafterUc_le_r0 hrest0_le
      have hafterUc_suf : IsDropSuffix x.bs afterUc := by
        have hs : IsDropSuffix rest0 afterUc := by
          rw [hrest0_eq]; unfold IsDropSuffix; simp [List.drop_left]
        exact suffix_trans hrest0_le hrest0_suf hafterUc_le_r0 hs
      have hafter0_le_uc : after0.length ≤ afterUc.length := by dsimp only [afterUc]; simp
      have hafter0_le : after0.length ≤ x.bs.length := Nat.le_trans hafter0_le_uc hafterUc_le
      have hafter0_suf : IsDropSuffix x.bs after0 := by
        have hs : IsDropSuffix afterUc after0 := by
          dsimp only [afterUc]; unfold IsDropSuffix; simp [List.drop_left]
        exact suffix_trans hafterUc_le hafterUc_suf hafter0_le_uc hs
      apply SepWPpLscro.weaken_pre
        (P' := e2b310_loopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr default
          x.bs (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            V1State.Unchunked.Ct1SentEkReceived.encodeRaw 1#32 ck.uc ++ afterUc) 0 0 0)
        (by dsimp only [e2b310_loopPre, sliceCursorAfter];
            rw [← hMsg, ← hrest0_eq, ← e2b310_tightPoolAt_of_vmPreserved hvm2]; sep_entail)
      refine e2b310_tag1_uc_opt_step_placed (outerLimit := after0.length)
        hVarintCall hBytesCall hAuthTight hFit
        (by dsimp only [e2b310_ownBytesOps] at hOps; omega)
        (by dsimp only [e2b310_ownBytesCum] at hCum; omega)
        (by dsimp only [e2b310_ownBytesMaxReq] at hReq; omega)
        hValidUcOpt hsp_align hbs_lt
        (by rw [← hrest0_eq]; exact hrest0_le)
        (by rw [← hrest0_eq]; exact hrest0_suf)
        hafter0_le_uc ?_
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm])
        (by simp only [arm64_norm, wp_norm, htrm])
        (by simp only [arm64_norm, wp_norm, hx19_m])
        (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hsm1, hsub0, hlim0_eq, hlim0_eq'])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      intro s_uc hpc_uc hrun_uc hsp_uc htr_uc hx19_uc hx20_uc hx21_uc hx22_uc hx23_uc hx24_uc hx25_uc hcs_uc
      refine e2b310_tag2_ct1_opt_step_placed (outerLimit := after0.length)
        hVarintCall hPolyTight hFit
        (by dsimp only [e2b310_ownBytesOps] at hOps; omega)
        (by dsimp only [e2b310_ownBytesCum] at hCum; omega)
        (by dsimp only [e2b310_ownBytesMaxReq] at hReq; omega)
        hValidEncOpt hsp_align hbs_lt56 hafterUc_le hafterUc_suf (Nat.le_refl _) ?_
        hpc_uc hrun_uc hsp_uc htr_uc hx19_uc hx20_uc hx21_uc hx22_uc hx23_uc hx24_uc hx25_uc hcs_uc
      intro s_end hpc_end hrun_end hsp_end htr_end hx19_end hx20_end hx21_end hx22_end hx23_end hx24_end hx25_end hcs_end
      have hck_eq : ({ uc := ck.uc, sendingCt1 := ck.sendingCt1 } : V1State.Chunked.EkReceivedCt1Sampled) = ck := by
        cases ck; rfl
      rw [hck_eq]
      exact e2b310_outer_exit_placed hDom hsp_align hmergeCk hafter0_le hafter0_suf
        hpc_end hrun_end hsp_end htr_end hx19_end hx20_end hx21_end hx22_end hx23_end hx24_end hx25_end hcs_end

end DomProof

/-- Fully `(maxOps, cumCap, maxReq)`-parametric guarded-tight verification of Block `310`
(`V1State.Chunked.EkReceivedCt1Sampled::merge`) on `(blkPC_310).rebase (blkPl_310).base H`. -/
theorem e2b310_chunkedEkReceivedCt1Sampled_merge_cl_placed_tight_of_contracts
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + e2b310_ownBytesOps + encOps ≤ maxOps)
    (hCum : authCum + e2b310_ownBytesCum + encCum ≤ cumCap)
    (hReq : max e2b310_ownBytesMaxReq (max authReq encReq) ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthLoose : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    (hPolyTight : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)))) :
    subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (blkPl_310).base
      (withLsCodeRoLoaded lsmpl
        (chunkedEkReceivedCt1SampledMergeSpecOfEnv A lim
          (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq)
          (e2b310_ChunkedEkReceivedCt1SampledGuardedEnv maxOps cumCap maxReq))) := by
  have hLoose := chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthLoose hPolyLoose
  have hDomOk := e2b310_dom_subroutine_ok hOps hCum hReq
    hVarintCall hBytesCall hAuthTight hPolyTight
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  by_cases hDom : tlb_ChunkedEkReceivedCt1SampledDom x
  · have hpreDom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
        (e2b310_DomSpec A lim maxOps cumCap maxReq)).pre (x, st) s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded, e2b310_DomSpec] at hpre ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _)))) hpre
    exact hDomOk.mono_outcome (x, st) R s0 hpc hrun hpreDom hsp fun _ hout => hout
  · have hpre1 : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
        (chunkedEkReceivedCt1SampledMergeSpec A lim)).pre (x, st) s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded, chunkedEkReceivedCt1SampledMergeSpec,
        chunkedEkReceivedCt1SampledMergeSpecOfEnv] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        tlb_fitsEnv_fallback_of_not_dom hDom h.2.2.2.2⟩)
    refine hLoose.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | hrest
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [withLsCodeRoLoaded, chunkedEkReceivedCt1SampledMergeSpec,
        chunkedEkReceivedCt1SampledMergeSpecOfEnv] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left ?_) hq
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      exact Entails.sepExists_elim fun evs => Entails.sepExists_right evs
        (sepConj_mono_left (Entails.pure_mono fun hevs =>
          Or.inr ⟨hDom, chunkedEkReceivedCt1SampledMergePostEnv_imp_pre hevs⟩))
    · exact Or.inr hrest

/-! ## 4. Own-Block `libsignalSessionLib.blockProgram` Tight Contracts -/

/-- `maxOps`-parametric own-block contract for `tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf`
on Block `310` (`authOps + 6 + encOps ≤ maxOps`). -/
theorem e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok_of_le
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {authOps encOps maxOps : Nat}
    (hOps : authOps + e2b310_ownBytesOps + encOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf A lim maxOps ext :=
  e2b310_own_of_blk_cro
    (e2b310_chunkedEkReceivedCt1Sampled_merge_cl_placed_tight_of_contracts
      hOps (by decide : 2952 + e2b310_ownBytesCum + 342615 ≤ 404301)
      (by decide : max e2b310_ownBytesMaxReq (max 32 2560) ≤ 2560)
      (e2b310_lift_cl_of_own hFrom) (e2b310_lift_cl_of_own hPush)
      (e2b310_lift_cl_of_own hVarint) (e2b310_lift_cl_of_own hSkip)
      (e2b310_lift_cro_of_own hBytes)
      (e2b310_lift_cro_of_own hAuthLoose) (e2b310_lift_cro_of_own hPolyLoose)
      (e2b310_lift_cro_of_own hAuthTight) (e2b310_lift_cro_of_own hPolyTight))

/-- Specialization of `e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok_of` at `maxOps := authOps + 6 + encOps`. -/
theorem e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok_of
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {authOps encOps : Nat}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOkOf A lim (authOps + 6 + encOps) ext :=
  e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok_of_le (Nat.le_refl _)
    hFrom hPush hVarint hSkip hBytes hAuthLoose hPolyLoose hAuthTight hPolyTight

/-- Default `2`-op/bytes specialization (`4 + 6 + 35 = 45` ops, `404,301` B, `2,560` B) for Block `310`,
matching `tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk A lim ext`. -/
theorem e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok
    [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext)
    (hPolyTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedEkReceivedCt1SampledMergePlacedTightOk A lim ext :=
  e2b310_chunkedEkReceivedCt1Sampled_merge_tight_placed_ok_of
    hFrom hPush hVarint hSkip hBytes hAuthLoose hPolyLoose hAuthTight hPolyTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB310PlacedBudget
