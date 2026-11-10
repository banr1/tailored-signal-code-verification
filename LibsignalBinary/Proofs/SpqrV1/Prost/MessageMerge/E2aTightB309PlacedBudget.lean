/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
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
# Guarded-Tight Placed Budget Proof for `Chunked.EkSentCt1Received::merge` (Block `309`)

Proves `tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf` on Block `309` within
`SpqrTightEvs maxOps 384723 2560` (`ucOps + decOps ≤ maxOps`, default `43 = 8 + 35`:
`Unchunked.EkSentCt1Received` `42,108` B + `PolynomialDecoder` `342,615` B) on canonical
`tlb_ChunkedEkSentCt1ReceivedDom` inputs, falling back to `ChunkedEkSentCt1ReceivedMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB309PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261
   instIsLsBlockProg_263 instIsLsBlockProg_291 instIsLsBlockProg_311 libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix iwt_w0_setWidth8
   key_shr32_of_lt key_wt_some sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAfter_join sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.ProtoRepr
  (optPolynomialDecoderPBAt polynomialDecoderPBAt vecVecU8Buf vecVecU8PinnedAt_eq_header_buf)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedEkSentCt1ReceivedMergeGhost ChunkedLoopRegs PolyDecoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedBelow chunkedBelow_eq_poly
   chunkedBelow_eq_unchunked chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedEkSentCt1ReceivedMerge_fnOff chunkedEkSentCt1ReceivedPBCapAt
   chunkedEkSentCt1ReceivedPBCapAt_mono chunkedMergeStack chunkedSavedRegs
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto instIsLsBlockProg_296
   memRegion_ekSentCt1Received_none_split memRegion_polyDecoder_none_split
   optPolyDecoderPtsLen optUnchunkedEkSentCt1ReceivedPBCapAt
   optUnchunkedEkSentCt1ReceivedPBCapAt_mono pointsTo64_zero_eq_pointsTo32_pair
   polyDecoderToProto protoPolynomialDecoderAt_eq_pb proto_mergeMessage_len_le
   proto_mergeMessage_suffix setWidth8_ofNat64_wt stackAt_chunkedMerge
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp unchunkedEkSentCt1ReceivedPBCapAt
   withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedEkSentCt1ReceivedMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkPC_309 blkPl_309 instIsLsBlockProg_309)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ChunkedEkSentCt1ReceivedDom tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf
   tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk
   tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf
   tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderMergePlacedTightOkOf
   tlb_UcEkSentCt1ReceivedDom tlb_UcEkSentCt1ReceivedGuardedEnvOf
   tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf
   tlb_ValidPolyDecoderPB tlb_ValidUcEkSentCt1ReceivedPB
   tlb_domHeap_of_dom tlb_fitsEnv_fallback_of_not_dom tlb_guardedEnv_tight_of_dom
   tlb_lenPrefixed tlb_optAuthZeroCapAt tlb_polyDecoderMergeTightSpecOfEnv
   tlb_polyDecoderZeroCapAt tlb_polyDecoderZeroCapAt_of_ptr
   tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv tlb_ucEkSentCt1ReceivedZeroCapAt
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedEkSentCt1ReceivedMergeEnv UnchunkedEkSentCt1ReceivedMergePostEnv
   chunkedEkSentCt1ReceivedMergePostEnv_imp_pre
   chunkedEkSentCt1ReceivedMergeSpec chunkedEkSentCt1ReceivedMergeSpecOfEnv
   decodeErrorPushMergeBudgetSpec unchunkedEkSentCt1ReceivedMergeSpec
   unchunkedEkSentCt1ReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedBudgetAux
  (stackAt_chunkedMerge_epilogue stackAt_decodeVarint2_raw_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1ReceivedClPlacedBudget
  (chunked_ek_sent_ct1_received_merge_cl_placed_ok_of_contracts)
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
  chunkedEkSentCt1ReceivedMerge_fnOff setWidth8_ofNat64_wt

@[local simp, local arm64_norm]
private theorem e2b309_iwt_w0_setWidth8_1 (iwt : WireType) :
    (BitVec.zeroExtend 64 ((BitVec.ofNat 64 iwt.toNat).setWidth 32)).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat :=
  (iwt_w0_setWidth8 iwt).1

@[local simp, local arm64_norm]
private theorem e2b309_iwt_w0_trunc32_zext64_setWidth8 (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

/-! ## 1. Private Own-Block ↔ Caller-Block Transfer Helpers (`e2b309_`) -/

private class e2b309_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 309 :=
  ⟨by decide, by decide, (instIsLsBlockProg_309 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b309_IsLsValidBlock 311 :=
  ⟨by decide, by decide, (instIsLsBlockProg_311 (fun _ => none)).externs_eq⟩

private theorem e2b309_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2b309_IsLsValidBlock j] {spec : Spec α}
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

private theorem e2b309_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2b309_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2b309_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2b309_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Zero-Cap Initializer Entailments, Tight `FitsEnv` Splits & Canonical Wire Lemmas -/

private theorem e2b309_pointsTo_zero_entails_vecU8ZeroCap (A : RustAlloc) (a ptr : BitVec 64)
    (hptr : ptr ≠ 0) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] := by
  refine Entails.trans ?_ (tlb_vecU8ZeroCapAt_of_ptr A a ptr [])
  rw [CryptoVerification.SpqrV1.Prost.MessageMerge.vecU8At_eq_header_sep_buf, vecHeader]
  unfold CryptoVerification.SpqrV1.Prost.MessageMerge.vecU8Buf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  refine Entails.trans ?_ (Entails.of_eq (sepConj_comm _ _))
  have hp : ([] : List (BitVec 8)).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  exact Entails.pure_right hp (Entails.refl _)

private theorem e2b309_default_ucEkSentCt1Received_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ∗
      ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 56#64) 40 ∗
      ((a + 96#64) ↦₆₄ 0#64) ⊢
      tlb_ucEkSentCt1ReceivedZeroCapAt A a default := by
  unfold tlb_ucEkSentCt1ReceivedZeroCapAt tlb_optAuthZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) [] ∗
    ((a + 48#64) ↦₆₄ 0xffffffffffffffff#64 ∗ memRegion (a + 48#64 + 8#64) 40) ∗
    ((a + 96#64) ↦₆₄ 0#64)
  have h1 := e2b309_pointsTo_zero_entails_vecU8ZeroCap A a 1#64 (by decide)
  have h2 := e2b309_pointsTo_zero_entails_vecU8ZeroCap A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  have h56 : a + 48#64 + 8#64 = a + 56#64 := by bv_lin
  rw [h32, h40] at h2; rw [h56]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

private theorem e2b309_pointsTo_zero_entails_polyVecVecU8PinnedZero (A : RustAlloc)
    (p ptr : BitVec 64) (hptr : ptr ≠ 0) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ ptr) ∗ ((p + 16#64) ↦₆₄ 0#64) ⊢
      CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, ptr⟩ p [] := by
  change _ ⊢ CryptoVerification.SpqrV1.ProtoRepr.vecVecU8PinnedAt A ⟨0#64, ptr⟩ p []
  rw [vecVecU8PinnedAt_eq_header_buf]
  unfold vecVecU8Buf vecBuf
  have hc0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [hc0, ↓reduceIte, sepConj_emp]
  have hp : ([] : List (List (BitVec 8))).length ≤ (0 : BitVec 64).toNat ∧
      (0 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ ptr ≠ 0 :=
    ⟨by decide, by decide, hptr⟩
  refine Entails.trans (Entails.pure_right hp (Entails.refl _)) ?_
  exact Entails.of_eq (by dsimp only [List.length]; sep_ac_rfl)

private theorem e2b309_default_polyDecoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7 ⊢
      tlb_polyDecoderZeroCapAt A p (polyDecoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyDecoderZeroCapAt_of_ptr A 8#64 p (polyDecoderToProto default))
  unfold CryptoVerification.SpqrV1.Poly.protoPolynomialDecoderPinnedAt
  change _ ⊢ CryptoVerification.SpqrV1.Poly.vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    ((p + 24#64) ↦₃₂ 0#32) ∗ ((p + 28#64) ↦₃₂ 0#32) ∗
    ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7
  have h1 := e2b309_pointsTo_zero_entails_polyVecVecU8PinnedZero A p 8#64 (by decide)
  have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
  rw [pointsTo64_zero_eq_pointsTo32_pair (p + 24#64), h28]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

private theorem e2b309_fitsEnv_decodeVarint2_of_some {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {maxOps : Nat}
    {evs₁ : List AllocEvent} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p)
    (hevs₁ : SpqrTightEvs maxOps 384723 2560 evs₁)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (DecodeVarint2Env bs) := by
  intro evs₂ h₂
  have hnil : evs₂ = [] := decodeVarint2Env_eq_nil_of_some hd h₂
  subst hnil
  exact ((fitsEvents_append M lim evs₁ [] st).mp
    (by simpa only [List.append_nil] using hFit evs₁ hevs₁)).2

private theorem e2b309_fitsEnv_uc_of_tight {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {ucOps decOps maxOps : Nat}
    {x_uc : UnchunkedEkSentCt1ReceivedMergeGhost}
    (hOps : ucOps + decOps ≤ maxOps)
    (hDomUc : tlb_UcEkSentCt1ReceivedDom x_uc)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560)) :
    FitsEnv M lim st (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps x_uc) := by
  intro evs₁ h₁
  have ht₁ : SpqrTightEvs ucOps 42108 2560 evs₁ := tlb_guardedEnv_tight_of_dom hDomUc h₁
  exact hFit evs₁
    (ht₁.mono (Nat.le_trans (Nat.le_add_right ucOps decOps) hOps) (by decide) (Nat.le_refl _))

private theorem e2b309_fitsEnv_poly_of_tight {M : AllocCostModel}
    {lim : BudgetLimits} {st : M.σ} {ucOps decOps maxOps : Nat}
    {evs₁ : List AllocEvent} {x_poly : PolyDecoderMergeGhost}
    (hOps : ucOps + decOps ≤ maxOps)
    (hevs₁ : SpqrTightEvs ucOps 42108 2560 evs₁)
    (hDomPoly : tlb_PolyDecoderDom x_poly)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560)) :
    FitsEnv M lim (M.stepEvents evs₁ st) (tlb_PolyDecoderGuardedEnvOf decOps x_poly) := by
  intro evs₂ h₂
  have ht₂ : SpqrTightEvs decOps 342615 2560 evs₂ := tlb_guardedEnv_tight_of_dom hDomPoly h₂
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp
    (hFit (evs₁ ++ evs₂) ((hevs₁.append ht₂).mono hOps (by decide) (by decide)))).2

private theorem e2b309_decodeVarint_lenPrefixed (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) =
      some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  have h1 : tlb_lenPrefixed raw rest =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint (BitVec.ofNat 64 raw.length) ++
        (raw ++ rest) := by
    simp only [tlb_lenPrefixed, List.append_assoc]
  rw [h1, ← proto_decodeVarint_toOption,
    CryptoVerification.SpqrV1Sync.Codec.proto_decodeVarint_encodeVarint]
  rfl

private theorem e2b309_decodeVarint_tag1_some {N : Type}
    (enc : N → List (BitVec 8)) (u : N) (tail : List (BitVec 8)) :
    decodeVarint
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage enc 1#32 (some u) ++ tail) =
      some (0x0a#64, tlb_lenPrefixed (enc u) tail) := by
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x0a#64 := by decide
  have heq :
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage enc 1#32 (some u) ++ tail =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x0a#64 ++
          tlb_lenPrefixed (enc u) tail := by
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk,
      tlb_lenPrefixed, List.append_nil, List.append_assoc]
  rw [heq, ← proto_decodeVarint_toOption,
    CryptoVerification.SpqrV1Sync.Codec.proto_decodeVarint_encodeVarint]
  rfl

private theorem e2b309_decodeVarint_tag3_some {N : Type}
    (enc : N → List (BitVec 8)) (d : N) (tail : List (BitVec 8)) :
    decodeVarint
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage enc 3#32 (some d) ++ tail) =
      some (0x1a#64, tlb_lenPrefixed (enc d) tail) := by
  have hk : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x1a#64 := by decide
  have heq :
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage enc 3#32 (some d) ++ tail =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint 0x1a#64 ++
          tlb_lenPrefixed (enc d) tail := by
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
      CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hk,
      tlb_lenPrefixed, List.append_nil, List.append_assoc]
  rw [heq, ← proto_decodeVarint_toOption,
    CryptoVerification.SpqrV1Sync.Codec.proto_decodeVarint_encodeVarint]
  rfl

private theorem e2b309_encodeOptMessage_some_length_gt {N : Type}
    (enc : N → List (BitVec 8)) (tag : BitVec 32) (v : N) (tail : List (BitVec 8)) :
    tail.length <
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage enc tag (some v) ++ tail).length := by
  have hv := (CryptoVerification.SpqrV1Sync.Codec.proto_encodeVarint_length
    (BitVec.ofNat 64 (enc v).length)).1
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, List.length_append]
  omega

private theorem e2b309_encodeRaw_le_lenPrefixed (raw tail : List (BitVec 8)) :
    raw.length ≤ (tlb_lenPrefixed raw tail).length := by
  simp only [tlb_lenPrefixed, List.length_append]
  omega

/-! ## 3. Canonical Domain (`tlb_ChunkedEkSentCt1ReceivedDom x`) Straight-Line Proof -/

private def e2b309_DomLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st_cur : M.σ) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64)
    (m : V1State.Chunked.EkSentCt1Received) (bs cur : List (BitVec 8)) : SepProp :=
  A.pool lim st_cur s ∗
    chunkedEkSentCt1ReceivedPBCapAt A.repAlloc msgPtr cur.length m ∗
    (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur ∗
    memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0

private noncomputable def e2b309_domSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) :
    Spec (ChunkedEkSentCt1ReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedEkSentCt1ReceivedDom x ∧
      (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      optPolyDecoderPtsLen x.msg.receivingCt2 + x.bs.length < 2 ^ 56 ∧
      FitsEnv M lim st (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps x)⌝ ∗
      chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp chunkedMergeStack
  post := (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
    (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)
    (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)).post

private theorem e2b309_dom_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (maxOps : Nat) (x : ChunkedEkSentCt1ReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.EkSentCt1Received) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedEkSentCt1ReceivedDom x)
    (hsome : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 384723 2560 evs) :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
    (e2b309_domSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2b309_domSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedMergeStack ∗
      (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedMergeStack ∗
          (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  refine sepConj_mono_right (sepConj_mono ?_
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))
  refine Entails.trans ?_ (Entails.sepExists_intro (P := fun evs' =>
    ⌜tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps x evs'⌝ ∗
      A.pool lim (M.stepEvents evs' st) sf) evs)
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.pure_right (Or.inl ⟨hDom, hevs⟩) (Entails.refl _)

section DomSteps

set_option quotPrecheck false in
local notation "entry" => (blkPl_309).base

private theorem e2b309_dom_exit_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {cur : List (BitVec 8)} {limit : Nat}
    {evs : List AllocEvent}
    (hDom : tlb_ChunkedEkSentCt1ReceivedDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (heq_lim : cur.length = limit)
    (hsome : (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hevs : SpqrTightEvs maxOps 384723 2560 evs)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hpc : s.pc = (blkPl_309).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (e2b309_DomLoopPre A lim (M.stepEvents evs st) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b309_DomLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedSavedRegs,
      sepConj_assoc, arm64_norm, hsp])
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
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt s0.sp chunkedMergeStack ∗
        (chunkedEkSentCt1ReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
          ((x.bufRef ↦₆₄ x.slot) ∗
            (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s)))
      by sep_ac_rfl))
      (e2b309_dom_ok_exit_entails A lim st maxOps x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b309_dom_decode_known_key_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hVarintCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st st_cur : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {iwt : WireType} {limit : Nat}
    (hFitDv : FitsEnv M lim st_cur (DecodeVarint2Env cur))
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag_ge1 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ s' : State,
      s'.pc = (blkPl_309).base + 244#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (e2b309_DomLoopPre A lim st_cur s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_309).base + 192#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (e2b309_DomLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag_ge1
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
    omega
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b309_DomLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedBelow_leaf s0.sp])
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st_cur))
      (ret_pc := entry + 212#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq,
            arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt hFitDv)
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
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hd hevs_dv
      (conv => arg 4; simp only [hevs_nil, AllocCostModel.stepEvents, List.foldl])
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b309_DomLoopPre A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2b309_DomLoopPre]; sep_entail)
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

private theorem e2b309_dom_tag1_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {ucOps decOps maxOps : Nat}
    (hOps : ucOps + decOps ≤ maxOps)
    (hUcTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps)
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps))))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {u : V1State.Unchunked.EkSentCt1Received}
    {rest cur₂ : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (huc_none : m.uc = none)
    (hValidUc : tlb_ValidUcEkSentCt1ReceivedPB u)
    (hrest_eq : rest = tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) cur₂)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evs₁ : List AllocEvent) (s' : State),
      SpqrTightEvs ucOps 42108 2560 evs₁ →
      s'.pc = (blkPl_309).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (e2b309_DomLoopPre A lim (M.stepEvents evs₁ st) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u } x.bs cur₂)
        (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_309).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 1)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (e2b309_DomLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_uc : UnchunkedEkSentCt1ReceivedMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr, default, x.bufRef, x.slot, restPtr, rest⟩
  have hDomUc : tlb_UcEkSentCt1ReceivedDom x_uc :=
    ⟨rfl, rfl, u, cur₂, hValidUc, hrest_eq⟩
  have hraw_le : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length ≤ rest.length := by
    rw [hrest_eq]; exact e2b309_encodeRaw_le_lenPrefixed _ _
  have hraw_lt64 : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length < 2 ^ 64 := by omega
  have huc_res :
      (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest 98).toOption =
      some (u, cur₂) := by
    have hm := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
      V1State.Unchunked.EkSentCt1Received.mergeField 1
      V1State.Unchunked.EkSentCt1Received.encodeRaw default u 98 cur₂
      (CryptoVerification.SpqrV1Sync.Codec.loopsTo_uc_ekSentCt1Received u hraw_lt64)
      hraw_lt64 (by decide)
    have hbs_uc : rest =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
          (BitVec.ofNat 64 (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length) ++
          (V1State.Unchunked.EkSentCt1Received.encodeRaw u ++ cur₂) := by
      simp only [hrest_eq, tlb_lenPrefixed, List.append_assoc]
    change (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
      .lengthDelimited default rest 98).toOption = some (u, cur₂)
    rw [hbs_uc, hm]; rfl
  have hcur₂_le : cur₂.length ≤ rest.length := proto_mergeMessage_len_le huc_res
  apply sepWPpLscro_of_vm (mid := entry + 308#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply sepWPpLscro_of_vm (mid := entry + 340#64)
    by_vm_steps
      (conv => arg 4; rw [e2b309_DomLoopPre,
        chunkedEkSentCt1ReceivedPBCapAt, huc_none,
        optUnchunkedEkSentCt1ReceivedPBCapAt, memRegion_ekSentCt1Received_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w96; apply SepWP.exists_elim; intro w48
      apply SepWP.exists_elim; intro w40; apply SepWP.exists_elim; intro w32
      apply SepWP.exists_elim; intro w24; apply SepWP.exists_elim; intro w16
      apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold (e2b309_default_ucEkSentCt1Received_entails_zeroCap A.repAlloc x.msgPtr)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply sepWPpLscro_of_vm (mid := lsmpl.base 311)
      by_vm_steps
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedBelow_eq_unchunked s0.sp])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro (x := (x_uc, st))
          (ret_pc := entry + 352#64) hUcTight
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv]
                rw [tlb_domHeap_of_dom hDomUc]
                dsimp only [x_uc]
                arg 2
                rw [A.pool_of_vmPreserved ((hvm0.trans hvm1).trans hvm2)]
                simp only [arm64_norm, wp_norm, hsp])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0],
            by simp only [arm64_norm, wp_norm, hx20],
            by simp only [arm64_norm, wp_norm, hx19],
            hrest_lt,
            e2b309_fitsEnv_uc_of_tight hOps hDomUc hFitTight⟩)
          (by dsimp only [x_uc, restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
          hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        apply sepWPpLscro_of_vm (mid := entry + 192#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv,
            unchunkedEkSentCt1ReceivedMergeSpecOfEnv, UnchunkedEkSentCt1ReceivedMergePostEnv,
            x_uc, huc_res, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs₁
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs₁_guard
          wp_focus_pure; intro hsm0
          have hevs₁ : SpqrTightEvs ucOps 42108 2560 evs₁ :=
            tlb_guardedEnv_tight_of_dom hDomUc hevs₁_guard
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hcur₂_le)
            (by dsimp only [restPtr]; sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← A.pool_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b309_DomLoopPre A lim (M.stepEvents evs₁ st) s0 _
              x.msgPtr x.bufRef x.slot x.ptr { m with uc := some u } x.bs cur₂)
            (Entails.of_eq (by
              dsimp only [e2b309_DomLoopPre, chunkedEkSentCt1ReceivedPBCapAt,
                optUnchunkedEkSentCt1ReceivedPBCapAt]
              rw [chunkedBelow_eq_unchunked]
              sep_ac_rfl))
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

private theorem e2b309_dom_tag3_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {ucOps decOps maxOps : Nat}
    (hOps : ucOps + decOps ≤ maxOps)
    (hPolyTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps)
          (tlb_PolyDecoderGuardedEnvOf decOps))))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkSentCt1Received} {d : PolynomialDecoder}
    {evs₁ : List AllocEvent} {rest rest_out : List (BitVec 8)} {limit : Nat}
    (hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (hevs₁ : SpqrTightEvs ucOps 42108 2560 evs₁)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpe_none : m.receivingCt2 = none)
    (hValidPoly : tlb_ValidPolyDecoderPB d)
    (hrest_eq : rest = tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) rest_out)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt56 : rest.length < 2 ^ 56)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evs₂ : List AllocEvent) (s' : State),
      SpqrTightEvs decOps 342615 2560 evs₂ →
      s'.pc = (blkPl_309).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s'
        (e2b309_DomLoopPre A lim (M.stepEvents (evs₁ ++ evs₂) st) s0 s'
          x.msgPtr x.bufRef x.slot x.ptr { m with receivingCt2 := some d } x.bs rest_out)
        (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_309).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s
      (e2b309_DomLoopPre A lim (M.stepEvents evs₁ st) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyDecoderMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr + 104#64, default, x.bufRef, x.slot, restPtr, rest⟩
  have hDomPoly : tlb_PolyDecoderDom x_poly :=
    ⟨rfl, rfl, d, rest_out, hValidPoly, hrest_eq⟩
  have hraw_le : (PolynomialDecoder.encodeRaw d).length ≤ rest.length := by
    rw [hrest_eq]; exact e2b309_encodeRaw_le_lenPrefixed _ _
  have hraw_lt64 : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64 := by omega
  have hpe_res :
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto WireType.lengthDelimited) default rest 98).toOption =
      some (d, rest_out) := by
    have hm := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
      PolynomialDecoder.mergeField 0
      PolynomialDecoder.encodeRaw default d 98 rest_out
      (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyDecoder d hraw_lt64)
      hraw_lt64 (by decide)
    have hbs_poly : rest =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
          (BitVec.ofNat 64 (PolynomialDecoder.encodeRaw d).length) ++
          (PolynomialDecoder.encodeRaw d ++ rest_out) := by
      simp only [hrest_eq, tlb_lenPrefixed, List.append_assoc]
    change (mergeMessage PolynomialDecoder.mergeField
      .lengthDelimited default rest 98).toOption = some (d, rest_out)
    rw [hbs_poly, hm]; rfl
  have hrest_out_le : rest_out.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
  apply sepWPpLscro_of_vm (mid := entry + 260#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply sepWPpLscro_of_vm (mid := entry + 284#64)
    by_vm_steps
      (conv => arg 4; rw [e2b309_DomLoopPre,
        chunkedEkSentCt1ReceivedPBCapAt, hpe_none,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split (x.msgPtr + 104#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w32; apply SepWP.exists_elim; intro w24
      apply SepWP.exists_elim; intro w16; apply SepWP.exists_elim; intro w8
      wp_steps
      apply SepWP.fold
        (e2b309_default_polyDecoder_entails_zeroCap A.repAlloc (x.msgPtr + 104#64))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
      by_vm_steps
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedBelow_eq_poly s0.sp])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro (x := (x_poly, M.stepEvents evs₁ st))
          (ret_pc := entry + 296#64) hPolyTight
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_polyDecoderMergeTightSpecOfEnv]
                rw [tlb_domHeap_of_dom hDomPoly]
                dsimp only [x_poly]
                arg 2
                rw [A.pool_of_vmPreserved ((hvm0.trans hvm1).trans hvm2)]
                simp only [arm64_norm, wp_norm, hsp])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0],
            by simp only [arm64_norm, wp_norm, hx20],
            by simp only [arm64_norm, wp_norm, hx19],
            by change 0 + rest.length < 2 ^ 56
               rw [Nat.zero_add]; exact hrest_lt56,
            e2b309_fitsEnv_poly_of_tight hOps hevs₁ hDomPoly hFitTight⟩)
          (by dsimp only [x_poly, restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
          hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        apply sepWPpLscro_of_vm (mid := entry + 192#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv,
            polyDecoderMergeSpecOfEnv, PolyDecoderMergePostEnv,
            x_poly, hpe_res, hsp, protoPolynomialDecoderAt_eq_pb,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs₂
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs₂_guard
          wp_focus_pure; intro hsm0
          have hevs₂ : SpqrTightEvs decOps 342615 2560 evs₂ :=
            tlb_guardedEnv_tight_of_dom hDomPoly hevs₂_guard
          (conv => arg 4; rw [← M.stepEvents_append]; simp only [arm64_norm, wp_norm, hsp])
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest_out_le)
            (by dsimp only [restPtr]; sep_focus)
          apply SepWP.fold
            (optUnchunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest_out_le)
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← A.pool_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b309_DomLoopPre A lim (M.stepEvents (evs₁ ++ evs₂) st) s0 _
              x.msgPtr x.bufRef x.slot x.ptr { m with receivingCt2 := some d } x.bs rest_out)
            (Entails.of_eq (by
              dsimp only [e2b309_DomLoopPre, chunkedEkSentCt1ReceivedPBCapAt,
                optPolynomialDecoderPBAt]
              rw [chunkedBelow_eq_poly]
              sep_ac_rfl))
          exact hcont evs₂ _ hevs₂
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

private theorem e2b309_dom_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {ucOps decOps maxOps : Nat}
    (hOps : ucOps + decOps ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hUcTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps)
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps))))
    (hPolyTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps)
          (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (blkPl_309).base
      (withLsCodeRoLoaded lsmpl (e2b309_domSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b309_domSpec
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨hDom, hx0_wt, hx1_msg, hx2_buf, hpts_0, hFitGuard⟩
  have hFitTight : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560) :=
    fun evs h => hFitGuard evs (Or.inl ⟨hDom, h⟩)
  obtain ⟨hwt_proto, hmsg_def, pb, rest_out, hValid, hbs_eq⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := by
    revert hwt_proto; cases x.wt <;> intro h <;> first | rfl | cases h
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  obtain ⟨raw, hraw_def⟩ : ∃ raw, raw = V1State.Chunked.EkSentCt1Received.encodeRaw pb := ⟨_, rfl⟩
  have hraw_le_bs : raw.length ≤ x.bs.length := by
    rw [hbs_eq, ← hraw_def]; exact e2b309_encodeRaw_le_lenPrefixed raw rest_out
  have hraw_lt64 : raw.length < 2 ^ 64 := by omega
  have hlen_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  obtain ⟨rest0, hrest0_raw⟩ : ∃ rest0, rest0 = raw ++ rest_out := ⟨_, rfl⟩
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, rest0) := by
    rw [hbs_eq, ← hraw_def, hrest0_raw]; exact e2b309_decodeVarint_lenPrefixed raw rest_out
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hge_len : ¬ rest0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_toNat, hrest0_raw, List.length_append]; omega
  have hule0 := ule_len_of_ge hge_len hrest0_lt
  have hsub0 := bv_len_sub_limit hge_len
  have hlim_eq : rest0.length - (BitVec.ofNat 64 raw.length).toNat = rest_out.length := by
    rw [hlen_toNat, hrest0_raw, List.length_append]; omega
  have hsome_top :
      (mergeMessage V1State.Chunked.EkSentCt1Received.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, rest_out) := by
    have hraw_pb_lt64 : (V1State.Chunked.EkSentCt1Received.encodeRaw pb).length < 2 ^ 64 := by
      rw [← hraw_def]; exact hraw_lt64
    have hm := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
      V1State.Chunked.EkSentCt1Received.mergeField 2
      V1State.Chunked.EkSentCt1Received.encodeRaw default pb 99 rest_out
      (CryptoVerification.SpqrV1Sync.Codec.loopsTo_ch_ekSentCt1Received pb hraw_pb_lt64)
      hraw_pb_lt64 (by decide)
    have hbs_top : x.bs =
        CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
          (BitVec.ofNat 64 (V1State.Chunked.EkSentCt1Received.encodeRaw pb).length) ++
          (V1State.Chunked.EkSentCt1Received.encodeRaw pb ++ rest_out) := by
      simp only [hbs_eq, tlb_lenPrefixed, List.append_assoc]
    rw [hwt_proto, hmsg_def, hbs_top, hm]; rfl
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
  obtain ⟨cur₂, hcur₂_raw⟩ : ∃ cur₂, cur₂ =
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialDecoder.encodeRaw 3#32 pb.receivingCt2 ++ rest_out := ⟨_, rfl⟩
  obtain ⟨m₁, hm₁_raw⟩ : ∃ m₁ : V1State.Chunked.EkSentCt1Received,
    m₁ = { uc := pb.uc, receivingCt2 := none } := ⟨_, rfl⟩
  have h_after_uc :
      ∀ (evs₁ : List AllocEvent) (s₁ : State),
        SpqrTightEvs ucOps 42108 2560 evs₁ →
        cur₂.length ≤ x.bs.length → IsDropSuffix x.bs cur₂ →
        s₁.pc = entry + 192#64 → s₁.status = .Running →
        s₁.sp = s0.sp - 128#64 → s₁.trace = s0.trace →
        s₁.readReg64 (Reg.gpr 19#5) = x.bufRef → s₁.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s₁.readReg64 (Reg.gpr 21#5) = x.slot →
        s₁.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_out.length →
        ChunkedLoopRegs s0 s₁ →
        SepWPpLscro lsmpl ((blkPC_309).rebase (blkPl_309).base H) (s0.readReg64 Reg.lr) s₁
          (e2b309_DomLoopPre A lim (M.stepEvents evs₁ st) s0 s₁
            x.msgPtr x.bufRef x.slot x.ptr m₁ x.bs cur₂)
          (WppPost (e2b309_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro evs₁ s₁ hevs₁ hcur₂_le hcur₂_suf hpc₁ hrun₁ hsp₁ htr₁ hx19₁ hx20₁ hx21₁ hx22₁ hcs₁
    rcases hpe : pb.receivingCt2 with _ | d
    · have hcur₂_eq : cur₂ = rest_out := by
        simp [hcur₂_raw, hpe, CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage]
      have hm₁_eq : m₁ = pb := by cases pb; subst hpe; exact hm₁_raw
      rw [hcur₂_eq] at hcur₂_le hcur₂_suf ⊢
      rw [hm₁_eq]
      exact e2b309_dom_exit_step
        ⟨hwt_proto, hmsg_def, pb, rest_out, hValid, hbs_eq⟩
        hsp_align rfl hsome_top
        (hevs₁.mono (Nat.le_trans (Nat.le_add_right ucOps decOps) hOps) (by decide) (Nat.le_refl _))
        hcur₂_le hcur₂_suf hpc₁ hrun₁ hsp₁ htr₁ hx21₁ hx22₁ hcs₁
    · have hValidPoly : tlb_ValidPolyDecoderPB d := hValid.2 d hpe
      have hcur₂_def : cur₂ =
          CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
            PolynomialDecoder.encodeRaw 3#32 (some d) ++ rest_out := by
        simp only [hcur₂_raw, hpe]
      obtain ⟨rest₃, hrest₃_def⟩ : ∃ rest₃,
        rest₃ = tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) rest_out := ⟨_, rfl⟩
      have hd_dv : decodeVarint cur₂ = some (0x1a#64, rest₃) := by
        rw [hcur₂_def, hrest₃_def]
        exact e2b309_decodeVarint_tag3_some PolynomialDecoder.encodeRaw d rest_out
      have hgt_lim₂ : ¬ cur₂.length ≤ rest_out.length := by
        have hgt := e2b309_encodeOptMessage_some_length_gt
          PolynomialDecoder.encodeRaw 3#32 d rest_out
        rw [← hcur₂_def] at hgt; omega
      have hcur₂_lt : cur₂.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur₂_le hbs_lt
      have hevs₁_max : SpqrTightEvs maxOps 384723 2560 evs₁ :=
        hevs₁.mono (Nat.le_trans (Nat.le_add_right ucOps decOps) hOps) (by decide) (Nat.le_refl _)
      have hFitDv₂ : FitsEnv M lim (M.stepEvents evs₁ st) (DecodeVarint2Env cur₂) :=
        e2b309_fitsEnv_decodeVarint2_of_some hd_dv hevs₁_max hFitTight
      have hrest₃_le_cur₂ : rest₃.length ≤ cur₂.length := Nat.le_of_lt (decodeVarint_length hd_dv)
      have hrest₃_le : rest₃.length ≤ x.bs.length := Nat.le_trans hrest₃_le_cur₂ hcur₂_le
      have hrest₃_lt56 : rest₃.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest₃_le hbs_lt56
      have hrest₃_suf : IsDropSuffix x.bs rest₃ :=
        suffix_trans hcur₂_le hcur₂_suf hrest₃_le_cur₂ (decodeVarint_suffix hd_dv)
      have hm₁_pe : m₁.receivingCt2 = none := by rw [hm₁_raw]
      refine e2b309_dom_decode_known_key_step (iwt := .lengthDelimited)
        hVarintCall hFitDv₂ hgt_lim₂ hsp_align hcur₂_le hcur₂_lt hcur₂_suf hd_dv
        (by decide) (by decide) (by decide) ?_
        hpc₁ hrun₁ hsp₁ htr₁ hx19₁ hx20₁ hx21₁ hx22₁ hcs₁
      intro s₂ hpc₂ hrun₂ hsp₂ htr₂ hx0₂ hx1₂ hx19₂ hx20₂ hx21₂ hx22₂ hcs₂
      refine e2b309_dom_tag3_some_step hOps hPolyTight hFitTight hevs₁ hsp_align
        hm₁_pe hValidPoly hrest₃_def hrest₃_le hrest₃_lt56 hrest₃_suf ?_
        hpc₂ hrun₂ hsp₂ htr₂ hx0₂ hx1₂ hx19₂ hx20₂ hx21₂ hx22₂ hcs₂
      intro evs₂ s₃ hevs₂ hpc₃ hrun₃ hsp₃ htr₃ _ _ hx21₃ hx22₃ hcs₃
      have hm_final : { m₁ with receivingCt2 := some d } = pb := by
        cases pb; subst hpe; rw [hm₁_raw]
      have hpf : rest_out.length ≤ rest₃.length ∧ IsDropSuffix rest₃ rest_out := by
        have hraw_d_lt64 : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64 := by
          have := e2b309_encodeRaw_le_lenPrefixed (PolynomialDecoder.encodeRaw d) rest_out
          rw [← hrest₃_def] at this; omega
        have hm_d := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
          PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw default d 98 rest_out
          (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyDecoder d hraw_d_lt64)
          hraw_d_lt64 (by decide)
        have hm_opt :
            (mergeMessage PolynomialDecoder.mergeField
              (codecWireTypeToProto WireType.lengthDelimited) default rest₃ 98).toOption =
            some (d, rest_out) := by
          have hr₃ : rest₃ =
              CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
                (BitVec.ofNat 64 (PolynomialDecoder.encodeRaw d).length) ++
                (PolynomialDecoder.encodeRaw d ++ rest_out) := by
            simp only [hrest₃_def, tlb_lenPrefixed, List.append_assoc]
          change (mergeMessage PolynomialDecoder.mergeField .lengthDelimited default rest₃ 98).toOption =
            some (d, rest_out)
          rw [hr₃, hm_d]; rfl
        exact proto_mergeMessage_suffix hm_opt
      have hrest_out_le : rest_out.length ≤ x.bs.length := Nat.le_trans hpf.1 hrest₃_le
      have hrest_out_suf : IsDropSuffix x.bs rest_out :=
        suffix_trans hrest₃_le hrest₃_suf hpf.1 hpf.2
      rw [hm_final]
      exact e2b309_dom_exit_step
        ⟨hwt_proto, hmsg_def, pb, rest_out, hValid, hbs_eq⟩
        hsp_align rfl hsome_top
        ((hevs₁.append hevs₂).mono hOps (by decide) (by decide))
        hrest_out_le hrest_out_suf hpc₃ hrun₃ hsp₃ htr₃ hx21₃ hx22₃ hcs₃
  have hrest0_box : Nonempty (rest0 =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 pb.uc ++ cur₂) :=
    ⟨by simp only [hrest0_raw, hraw_def, hcur₂_raw, V1State.Chunked.EkSentCt1Received.encodeRaw,
          List.append_assoc]⟩
  clear hraw_def hrest0_raw
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
             e2b309_fitsEnv_decodeVarint2_of_some hdv0 (SpqrTightEvs.nil maxOps 384723 2560) hFitTight⟩)
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
      have hevs_nil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      (conv => arg 4; simp only [hevs_nil, AllocCostModel.stepEvents, List.foldl])
      apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedEkSentCt1ReceivedPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le)
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← A.pool_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b309_DomLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs rest0)
        (Entails.of_eq (by
          dsimp only [e2b309_DomLoopPre]
          rw [hmsg_def, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
          sep_ac_rfl))
      have hlim_raw : rest0.length - raw.length = rest_out.length := by
        rw [← hlen_toNat]; exact hlim_eq
      obtain ⟨hrest0_def⟩ := hrest0_box
      rcases huc : pb.uc with _ | u
      · have hrest0_eq_cur₂ : rest0 = cur₂ := by
          simp only [hrest0_def, huc,
            CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
        have hm₀_eq_m₁ : (default : V1State.Chunked.EkSentCt1Received) = m₁ := by
          rw [hm₁_raw, huc]; rfl
        have hcur₂_le : cur₂.length ≤ x.bs.length := hrest0_eq_cur₂ ▸ hrest0_le
        have hcur₂_suf : IsDropSuffix x.bs cur₂ := hrest0_eq_cur₂ ▸ hrest0_suf
        refine SepWPpLscro.weaken_pre
          (Entails.of_eq (by rw [hrest0_eq_cur₂, hm₀_eq_m₁]; rfl))
          (h_after_uc [] _ (SpqrTightEvs.nil ucOps 42108 2560)
            hcur₂_le hcur₂_suf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩)
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hrunm]
        · simp only [arm64_norm, wp_norm, hspm]
        · simp only [arm64_norm, wp_norm, htrm]
        · simp only [arm64_norm, wp_norm, hx19_m]
        · simp only [arm64_norm, wp_norm, hx20_m]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hsm1, hsub0, hlen_toNat, hlim_raw]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm]
        · simp only [arm64_norm, wp_norm, hx26_m]
        · simp only [arm64_norm, wp_norm, hx27_m]
        · simp only [arm64_norm, wp_norm, hx28_m]
        · simp only [arm64_norm, wp_norm, hvregs_m]
      · have hValidUc : tlb_ValidUcEkSentCt1ReceivedPB u := hValid.1 u huc
        have hrest0_some : rest0 =
            CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
              V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 (some u) ++ cur₂ := by
          simp only [hrest0_def, huc]
        obtain ⟨rest₁, hrest₁_def⟩ : ∃ rest₁,
          rest₁ = tlb_lenPrefixed (V1State.Unchunked.EkSentCt1Received.encodeRaw u) cur₂ := ⟨_, rfl⟩
        have hd_u : decodeVarint rest0 = some (0x0a#64, rest₁) := by
          rw [hrest0_some, hrest₁_def]
          exact e2b309_decodeVarint_tag1_some
            V1State.Unchunked.EkSentCt1Received.encodeRaw u cur₂
        have hgt_lim₁ : ¬ rest0.length ≤ rest_out.length := by
          have hgt := e2b309_encodeOptMessage_some_length_gt
            V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 u cur₂
          have hcur₂_ge : rest_out.length ≤ cur₂.length := by
            rw [hcur₂_raw, List.length_append]; omega
          rw [← hrest0_some] at hgt; omega
        have hFitDv₁ : FitsEnv M lim st (DecodeVarint2Env rest0) := by
          simpa only [AllocCostModel.stepEvents, List.foldl] using
            e2b309_fitsEnv_decodeVarint2_of_some hd_u (SpqrTightEvs.nil maxOps 384723 2560) hFitTight
        have hrest₁_le_rest0 : rest₁.length ≤ rest0.length := Nat.le_of_lt (decodeVarint_length hd_u)
        have hrest₁_le : rest₁.length ≤ x.bs.length := Nat.le_trans hrest₁_le_rest0 hrest0_le
        have hrest₁_lt : rest₁.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest₁_le hbs_lt
        have hrest₁_suf : IsDropSuffix x.bs rest₁ :=
          suffix_trans hrest0_le hrest0_suf hrest₁_le_rest0 (decodeVarint_suffix hd_u)
        refine e2b309_dom_decode_known_key_step (iwt := .lengthDelimited)
          hVarintCall hFitDv₁ hgt_lim₁ hsp_align hrest0_le hrest0_lt hrest0_suf hd_u
          (by decide) (by decide) (by decide) ?_
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hsm1, hsub0, hlen_toNat, hlim_raw])
          ⟨by simp only [arm64_norm, wp_norm],
           by simp only [arm64_norm, wp_norm],
           by simp only [arm64_norm, wp_norm],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩
        intro s_u hpc_u hrun_u hsp_u htr_u hx0_u hx1_u hx19_u hx20_u hx21_u hx22_u hcs_u
        refine e2b309_dom_tag1_some_step hOps hUcTight hFitTight hsp_align
          rfl hValidUc hrest₁_def hrest₁_le hrest₁_lt hrest₁_suf ?_
          hpc_u hrun_u hsp_u htr_u hx0_u hx1_u hx19_u hx20_u hx21_u hx22_u hcs_u
        intro evs₁ s₁ hevs₁ hpc₁ hrun₁ hsp₁ htr₁ hx19₁ hx20₁ hx21₁ hx22₁ hcs₁
        have huf : cur₂.length ≤ rest₁.length ∧ IsDropSuffix rest₁ cur₂ := by
          have hraw_u_lt64 : (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length < 2 ^ 64 := by
            have := e2b309_encodeRaw_le_lenPrefixed
              (V1State.Unchunked.EkSentCt1Received.encodeRaw u) cur₂
            rw [← hrest₁_def] at this; omega
          have hm_u := CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
            V1State.Unchunked.EkSentCt1Received.mergeField 1
            V1State.Unchunked.EkSentCt1Received.encodeRaw default u 98 cur₂
            (CryptoVerification.SpqrV1Sync.Codec.loopsTo_uc_ekSentCt1Received u hraw_u_lt64)
            hraw_u_lt64 (by decide)
          have hm_opt :
              (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
                (codecWireTypeToProto WireType.lengthDelimited) default rest₁ 98).toOption =
              some (u, cur₂) := by
            have hr₁ : rest₁ =
                CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
                  (BitVec.ofNat 64 (V1State.Unchunked.EkSentCt1Received.encodeRaw u).length) ++
                  (V1State.Unchunked.EkSentCt1Received.encodeRaw u ++ cur₂) := by
              simp only [hrest₁_def, tlb_lenPrefixed, List.append_assoc]
            change (mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField
              .lengthDelimited default rest₁ 98).toOption = some (u, cur₂)
            rw [hr₁, hm_u]; rfl
          exact proto_mergeMessage_suffix hm_opt
        have hcur₂_le : cur₂.length ≤ x.bs.length := Nat.le_trans huf.1 hrest₁_le
        have hcur₂_suf : IsDropSuffix x.bs cur₂ := suffix_trans hrest₁_le hrest₁_suf huf.1 huf.2
        have hm₁_eq : { (default : V1State.Chunked.EkSentCt1Received) with uc := some u } = m₁ := by
          rw [hm₁_raw, huc]; rfl
        rw [hm₁_eq]
        exact h_after_uc evs₁ s₁ hevs₁ hcur₂_le hcur₂_suf
          hpc₁ hrun₁ hsp₁ htr₁ hx19₁ hx20₁ hx21₁ hx22₁ hcs₁

end DomSteps

/-! ## 4. Non-Domain (`¬ tlb_ChunkedEkSentCt1ReceivedDom x`) Fallback -/

private theorem e2b309_not_dom_reaches_outcome [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps : Nat}
    (hLoose : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (blkPl_309).base
      (withLsCodeRoLoaded lsmpl (chunkedEkSentCt1ReceivedMergeSpec A lim)))
    {x : ChunkedEkSentCt1ReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    (hNotDom : ¬ tlb_ChunkedEkSentCt1ReceivedDom x)
    (hpc : s0.pc = (blkPl_309).base)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
      (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)
        (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps))).pre (x, st) s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome ((blkPC_309).rebase (blkPl_309).base H)
      (withLsCodeRoLoaded lsmpl
        (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)))
      (x, st) R s0 s0 := by
  have hpre1 : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
      (chunkedEkSentCt1ReceivedMergeSpec A lim)).pre (x, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [chunkedEkSentCt1ReceivedMergeSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv]
    exact sepConj_mono_left (Entails.pure_mono fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      tlb_fitsEnv_fallback_of_not_dom hNotDom h.2.2.2.2⟩)
  refine hLoose.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))) hq
    exact Entails.sepExists_elim fun evs => Entails.sepExists_right evs
      (sepConj_mono_left (Entails.pure_mono fun hevs =>
        Or.inr ⟨hNotDom, chunkedEkSentCt1ReceivedMergePostEnv_imp_pre hevs⟩))
  · exact Or.inr hrest

/-! ## 5. Block `309` Tight Placed Contracts (`V1State.Chunked.EkSentCt1Received::merge`) -/

/-- Block `309` (`V1State.Chunked.EkSentCt1Received::merge`) `maxOps`-parametric tight contract on
`((blkPC_309).rebase (blkPl_309).base H)` for any `maxOps` with `ucOps + decOps ≤ maxOps`:
`ucOps + decOps` non-free ops (default `8 + 35 = 43`), `cumCap = 384,723` B, `maxReq = 2,560` B. -/
theorem e2b309_chunkedEkSentCt1Received_merge_tight_blk309_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {ucOps decOps maxOps : Nat}
    (hOps : ucOps + decOps ≤ maxOps)
    (hFromCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcLoose : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyLoose : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl
        (tlb_ucEkSentCt1ReceivedMergeTightSpecOfEnv A lim
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps)
          (tlb_UcEkSentCt1ReceivedGuardedEnvOf ucOps))))
    (hPolyTight : subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps)
          (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_309).rebase (blkPl_309).base H) (blkPl_309).base
      (withLsCodeRoLoaded lsmpl
        (chunkedEkSentCt1ReceivedMergeSpecOfEnv A lim
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps)
          (tlb_ChunkedEkSentCt1ReceivedGuardedEnvOf maxOps))) := by
  have hLoose := chunked_ek_sent_ct1_received_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hUcLoose hPolyLoose
  have hDomOk := e2b309_dom_subroutine_ok hOps hVarintCall hUcTight hPolyTight
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  by_cases hDom : tlb_ChunkedEkSentCt1ReceivedDom x
  · have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl
        (e2b309_domSpec A lim maxOps)).pre (x, st) s0 ∗ R := by
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      dsimp only [e2b309_domSpec, chunkedEkSentCt1ReceivedMergeSpecOfEnv]
      exact sepConj_mono_left (Entails.pure_mono fun h => ⟨hDom, h⟩)
    exact hDomOk.mono_outcome (x, st) R s0 hpc hrun hpre_dom hsp fun _ hout => hout
  · exact e2b309_not_dom_reaches_outcome hLoose hDom hpc hrun hpre hsp

/-- `maxOps`-monotone own-block tight contract for Block `309` (`V1State.Chunked.EkSentCt1Received::merge`, `ucOps + decOps ≤ maxOps`). -/
theorem e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok_le [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ucOps decOps maxOps : Nat}
    (hOps : ucOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUcLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim ucOps ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf A lim maxOps ext :=
  e2b309_own_of_blk_cro (e2b309_chunkedEkSentCt1Received_merge_tight_blk309_ok_of_contracts hOps
    (e2b309_lift_cl_of_own hFrom) (e2b309_lift_cl_of_own hPush)
    (e2b309_lift_cl_of_own hVarint) (e2b309_lift_cl_of_own hSkip)
    (e2b309_lift_cro_of_own hUcLoose) (e2b309_lift_cro_of_own hPolyLoose)
    (e2b309_lift_cro_of_own hUcTight) (e2b309_lift_cro_of_own hPolyTight))

/-- `maxOps`-parametric own-block tight contract for Block `309` (`V1State.Chunked.EkSentCt1Received::merge`) at `ucOps + decOps`. -/
theorem e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {ucOps decOps : Nat}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hUcLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim ucOps ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOkOf A lim (ucOps + decOps) ext :=
  e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok_le (Nat.le_refl _)
    hFrom hPush hVarint hSkip hUcLoose hPolyLoose hUcTight hPolyTight

/-- Default `2`-op/bytes specialization (`8 + 35 = 43` ops, `384,723` B, `2,560` B) for Block `309`. -/
theorem e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok [LibsignalPlacement]
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
    (hUcLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311) (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)))
    (hPolyLoose : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hUcTight : tlb_UcEkSentCt1ReceivedMergePlacedTightOkOf A lim 8 ext)
    (hPolyTight : tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedEkSentCt1ReceivedMergePlacedTightOk A lim ext :=
  e2b309_chunkedEkSentCt1Received_merge_tight_placed_ok_of
    hFrom hPush hVarint hSkip hUcLoose hPolyLoose hUcTight hPolyTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB309PlacedBudget
