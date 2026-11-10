/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304UcPlacedBudget
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
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.KeysSampled::merge` (Block `304`)

Proves `tlb_ChunkedKeysSampledMergePlacedTightOkOf` on Block `304` within
`SpqrTightEvs maxOps 384723 2560` (`authOps + 4 + encOps ≤ maxOps`, default `43 = 4 + 4 + 35`:
inlined `Unchunked.HeaderSent` `42,108` B + `PolynomialEncoder` `342,615` B) on canonical
`tlb_ChunkedKeysSampledDom` inputs, falling back to `ChunkedKeysSampledMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open scoped LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux
open CryptoVerification (ls_externAt?_blockProgram_eq_of_externs_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudget (chunked_keys_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common (b304PoolAt b304PoolAt_eq_of_vmPreserved b304PoolAt_init b304PoolAt_mono b304PoolAt_step b304PoolAt_step_nil b304_fitsEnv_decodeVarint2_of_some b304_fitsEnv_step_tight codec_decodeVarint_encodeVarint codec_decodeVarint_tlb_lenPrefixed encodeOptMessage_tag1_some encodeOptMessage_tag2_some proto_mergeMessage_keysSampled_canonical proto_mergeMessage_polyEncoder_canonical validChunkedKeysSampledPB_encodeRaw_len_le)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_261 instIsLsBlockProg_263
   instIsLsBlockProg_290 instIsLsBlockProg_291 instIsLsBlockProg_295 libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack extract_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix
   key_shr32_of_lt key_wt_some pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.RecordCodecs.Placed (instIsLsBlockProg_257)
open CryptoVerification.LibsignalSpqrV1 (PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeOptMessage encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialEncoderAt protoPolynomialEncoderIdxOff protoPolynomialEncoderPadOff
   protoPolynomialEncoderPadSize protoPolynomialEncoderPinnedAt
   protoPolynomialEncoderPolysOff vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedInl10CalleeSaved ChunkedKeysSampledMergeGhost OptPolyEncoderBound
   PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedInlBelowStack
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails chunkedInlBelow_eq_polyMerge
   chunkedInlSavedRegs10 chunkedInlStack chunkedKeysSampledMerge_fnOff
   chunkedKeysSampledPBCapAt chunkedKeysSampledPBCapAt_mono
   cmp_len_limit_of_eq cmp_len_limit_of_gt codecWireTypeToProto
   instIsLsBlockProg_297 memRegion_polyEncoder_none_split_inl
   optHeaderSentPBCapAt optHeaderSentPBCapAt_mono
   optPolyEncoderPolysLen optPolyEncoderPtsLen optPolynomialEncoderPBAt_some_eq
   polyEncoderToProto proto_mergeMessage_suffix
   stackAt_chunkedInl10_epilogue stackAt_chunkedInl_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
  (blkPC_304 blkPl_304 instIsLsBlockProg_304)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOk tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedKeysSampledDom tlb_ChunkedKeysSampledGuardedEnvOf
   tlb_ChunkedKeysSampledMergePlacedTightOk tlb_ChunkedKeysSampledMergePlacedTightOkOf
   tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf
   tlb_PolyEncoderMergePlacedTightOk tlb_PolyEncoderMergePlacedTightOkOf
   tlb_PolyEncoderTightEnvOf tlb_ValidChunkedKeysSampledPB tlb_ValidPolyEncoderPB
   tlb_ValidUcHeaderSentPB tlb_authMergeTightSpecOfEnv
   tlb_domHeap_of_dom tlb_fitsEnv_fallback_of_not_dom
   tlb_fitsEnv_guarded_of_dom tlb_guardedEnv_tight_of_dom tlb_lenPrefixed
   tlb_polyEncoderMergeTightSpecOfEnv tlb_polyEncoderZeroCapAt
   tlb_polyEncoderZeroCapAt_of_ptrs)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedKeysSampledMergePostEnv_imp_pre chunkedKeysSampledMergeSpec
   chunkedKeysSampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledBudgetAux
  (setWidth8_zext64_trunc32_ofNat64_wt_ks)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledClPlacedBudget
  (chunked_keys_sampled_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304UcPlacedBudget
  (b304UcPre b304_uc_canonical_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyEncoderMergePostEnv bytesMerge3RawBudgetSpec polyEncoderMergeSpec
   polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem isDropSuffix_append_right (a b : List (BitVec 8)) :
    IsDropSuffix (a ++ b) b := by
  unfold IsDropSuffix
  have hsub : (a ++ b).length - b.length = a.length := by
    rw [List.length_append]; omega
  rw [hsub, List.drop_left]

/-! ## 1. Own-Block ↔ Caller-Block Transfer Helpers (`e2b304_`) -/

private class e2b304_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 257 :=
  ⟨by decide, by decide, (instIsLsBlockProg_257 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 261 :=
  ⟨by decide, by decide, (instIsLsBlockProg_261 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 263 :=
  ⟨by decide, by decide, (instIsLsBlockProg_263 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 290 :=
  ⟨by decide, by decide, (instIsLsBlockProg_290 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 297 :=
  ⟨by decide, by decide, (instIsLsBlockProg_297 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b304_IsLsValidBlock 304 :=
  ⟨by decide, by decide, (instIsLsBlockProg_304 (fun _ => none)).externs_eq⟩

private theorem e2b304_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2b304_IsLsValidBlock j] {spec : Spec α}
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

private theorem e2b304_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2b304_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2b304_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2b304_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

/-! ## 2. Zero-Cap `PolynomialEncoder` Init & Canonical Post Entailment -/

private theorem e2b304_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b304_default_polyEncoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_
    (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + protoPolynomialEncoderPolysOff) [] ∗
    ((p + protoPolynomialEncoderIdxOff) ↦₃₂ 0#32) ∗
    memRegion (p + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize
  dsimp only [protoPolynomialEncoderPolysOff, protoPolynomialEncoderIdxOff,
    protoPolynomialEncoderPadOff, protoPolynomialEncoderPadSize]
  have h1 := e2b304_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h2 := e2b304_pointsTo_zero_entails_vecVecU8ZeroPin A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

private noncomputable def e2b304_domSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedKeysSampledMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedKeysSampledDom x⌝ ∗
      (chunkedKeysSampledMergeSpecOfEnv A lim
        (tlb_ChunkedKeysSampledGuardedEnvOf maxOps)
        (tlb_ChunkedKeysSampledGuardedEnvOf maxOps)).pre (x, st) s
  post :=
    (chunkedKeysSampledMergeSpecOfEnv A lim
      (tlb_ChunkedKeysSampledGuardedEnvOf maxOps)
      (tlb_ChunkedKeysSampledGuardedEnvOf maxOps)).post

private theorem e2b304_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (maxOps : Nat) (x : ChunkedKeysSampledMergeGhost)
    (s0 s sf : State) (m : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedKeysSampledDom x)
    (hsome : (mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 384723 2560 evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
      (e2b304_domSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2b304_domSpec, chunkedKeysSampledMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  have hPost : tlb_ChunkedKeysSampledGuardedEnvOf maxOps x evs := Or.inl ⟨hDom, hevs⟩
  have hPool : A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜tlb_ChunkedKeysSampledGuardedEnvOf maxOps x evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf := by
    refine Entails.sepExists_right evs ?_
    exact Entails.pure_right hPost (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono hPool
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

/-! ## 3. Canonical Outer Loop Steps (`+168 → +228`, Tag `2` `sendingHdr`, `+168 → ret`) -/

section DomSteps

open scoped LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampledUcBudgetAux

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedKeysSampledMerge_fnOff

set_option quotPrecheck false in
local notation "entry" => (blkPl_304).base

private def b304OuterPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (x : ChunkedKeysSampledMergeGhost)
    (m : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) (cur : List (BitVec 8)) (ops cum : Nat) : SepProp :=
  chunkedKeysSampledPBCapAt A.repAlloc x.msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
    sliceCursorAfter x.slot x.ptr x.bs cur ∗
    b304PoolAt A lim st ops cum s

private theorem b304_outer_step_key_varint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {m : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {outerLimit ops cum : Nat}
    (hgt_lim : outerLimit < cur.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : key.toNat < 2 ^ 32)
    (hwt : CryptoVerification.LibsignalProtoCodec.WireType.ofNat? (key.toNat % 8) = some .lengthDelimited)
    (htag_pos : 1 ≤ key.toNat / 8)
    (hcont : ∀ s' : State,
      s'.pc = entry + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = 2#64 →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304OuterPre A lim st s0 s' x m rest ops cum) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304OuterPre A lim st s0 s x m cur ops cum) Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
  have hnle_lim : ¬ cur.length ≤ outerLimit := by omega
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hnle_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [b304OuterPre, b304PoolAt,
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
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq,
            arm64_norm, wp_norm, hsp, hx19]; try rfl)
      (And.intro hcur_lt (b304_fitsEnv_decodeVarint2_of_some hd))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
    have hk_ge : ¬ 2 ^ 32 ≤ key.toNat := by omega
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    have hitag0 : ¬ key.toNat / 8 < 1 := by omega
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
    apply sepWPpLscro_of_vm (mid := entry + 228#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedKeysSampledPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := b304OuterPre A lim st s0 _ x m rest ops cum)
        (by dsimp only [b304OuterPre]; sep_entail)
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

private theorem b304_outer_tag2_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : authOps + 4 + encOps ≤ maxOps)
    (hEncTightCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps))))
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {ucOpt : Option CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent}
    {e : PolynomialEncoder} {restOut : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560))
    (he : tlb_ValidPolyEncoderPB e)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hrest_le : (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e) restOut).length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e) restOut))
    (hcont : ∀ s' : State,
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 restOut.length →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s'
        (b304OuterPre A lim st s0 s' x { uc := ucOpt, sendingHdr := some e }
          restOut maxOps 384723) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = 2#64)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 restOut.length)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304OuterPre A lim st s0 s x { uc := ucOpt, sendingHdr := none }
        (tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e) restOut) (authOps + 4) 42108)
      Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let rest := tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e) restOut
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyEncoderMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr + 104#64, default, x.bufRef, x.slot, restPtr, rest⟩
  have hPolyDom : tlb_PolyEncoderDom x_poly := ⟨rfl, rfl, e, restOut, he, rfl⟩
  have hpoly_res :
      (mergeMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.mergeField
        (codecWireTypeToProto (.lengthDelimited : WireType)) default rest 98).toOption =
        some (e, restOut) :=
    proto_mergeMessage_polyEncoder_canonical e restOut he
  have hrestOut_le : restOut.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
  apply sepWPpLscro_of_vm (mid := entry + 244#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := b304OuterPre A lim st s0 _ x { uc := ucOpt, sendingHdr := none } rest (authOps + 4) 42108)
      (by dsimp only [b304OuterPre]; rw [b304PoolAt_eq_of_vmPreserved hvm0]; exact Entails.refl _)
    apply sepWPpLscro_of_vm (mid := entry + 272#64)
    by_vm_steps
      (conv => arg 4; rw [b304OuterPre, chunkedKeysSampledPBCapAt,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split_inl (x.msgPtr + 104#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
      apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := e2b304_default_polyEncoder_entails_zeroCap A.repAlloc (x.msgPtr + 104#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm1]
      apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
      by_vm_steps
        (conv => arg 4; rw [b304PoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedInlBelow_eq_polyMerge s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
        apply SepWP.exists_elim; intro evs
        apply SepWP.pure_elim; intro hevs
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        have hFitPoly : FitsEnv M lim (M.stepEvents evs st)
            (tlb_PolyEncoderGuardedEnvOf encOps x_poly) :=
          tlb_fitsEnv_guarded_of_dom hPolyDom
            (b304_fitsEnv_step_tight hFit hevs (fun _ h => h) hOps
              (by decide : 42108 + 342615 ≤ 384723) (Nat.le_refl 2560))
        have hpts_bound : x_poly.msg.pts.length + x_poly.bs.length < 2 ^ 56 := by
          have h0 : (default : PolynomialEncoder).pts.length = 0 := rfl
          dsimp only [x_poly, rest]; rw [h0]; omega
        have hpolys_bound : x_poly.msg.polys.length + x_poly.bs.length < 2 ^ 56 := by
          have h0 : (default : PolynomialEncoder).polys.length = 0 := rfl
          dsimp only [x_poly, rest]; rw [h0]; omega
        refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
          (ret_pc := entry + 288#64) hEncTightCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_polyEncoderMergeTightSpecOfEnv, x_poly]
                rw [tlb_domHeap_of_dom hPolyDom]
                simp only [sepConj_assoc]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, arm64_norm, wp_norm, hsp])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx8],
            by simp only [arm64_norm, wp_norm, hx20],
            by simp only [arm64_norm, wp_norm, hx19],
            hpts_bound,
            hpolys_bound,
            hFitPoly⟩)
          (by dsimp only [x_poly, rest, restPtr, sliceCursorAt]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
          hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
        apply sepWPpLscro_of_vm (mid := entry + 168#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv, polyEncoderMergeSpecOfEnv,
            PolyEncoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_p
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_g
          wp_focus_pure; intro hsm0
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
          have hevs_p : SpqrTightEvs encOps 342615 2560 evs_p :=
            tlb_guardedEnv_tight_of_dom hPolyDom hevs_g
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrestOut_le)
            (by dsimp only [rest]; sep_focus)
          apply SepWP.fold (optHeaderSentPBCapAt_mono A.repAlloc x.msgPtr ucOpt hrestOut_le)
            (by dsimp only [rest]; sep_focus)
          apply SepWP.fold
            (Entails.trans
              (b304PoolAt_step A lim st (LibsignalBinary.Heap.VmPreserved.refl sm) hevs hevs_p (Nat.le_refl 2560))
              (b304PoolAt_mono A lim st hOps (by decide : 42108 + 342615 ≤ 384723) sm))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← b304PoolAt_eq_of_vmPreserved hvm3]
          apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
            (P' := b304OuterPre A lim st s0 _ x { uc := ucOpt, sendingHdr := some e }
              restOut maxOps 384723)
            (by dsimp only [b304OuterPre, chunkedKeysSampledPBCapAt];
                rw [optPolynomialEncoderPBAt_some_eq]; simp only [arm64_norm]; sep_entail)
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
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem b304_outer_eq_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedKeysSampledMergeGhost} {st : M.σ} {R : SepProp}
    {s0 s : State} {m : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled} {cur : List (BitVec 8)}
    (hDom : tlb_ChunkedKeysSampledDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsome : (mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 cur.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s
      (b304OuterPre A lim st s0 s x m cur maxOps 384723)
      (WppPost (e2b304_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : cur.length = cur.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [b304OuterPre, b304PoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlSavedRegs10,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      sepConj_pure_left_comm, arm64_norm, hsp])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0)
      (by unfold chunkedInlSavedRegs10; sep_focus)
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
      by simp only [CalleeSavedPreserved, arm64_norm, wp_norm, hx27, hx28, hvregs]⟩
    refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (e2b304_ok_exit_entails A lim st maxOps x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b304_dom_blk_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps encOps maxOps : Nat} (hOps : authOps + 4 + encOps ≤ maxOps)
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hEncTightCall : subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_PolyEncoderGuardedEnvOf encOps) (tlb_PolyEncoderGuardedEnvOf encOps)))) :
    subroutine_ok ((blkPC_304).rebase (blkPl_304).base H) (blkPl_304).base
      (withLsCodeRoLoaded lsmpl (e2b304_domSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b304_domSpec chunkedKeysSampledMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b304_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  dsimp only [e2b304_domSpec, chunkedKeysSampledMergeSpecOfEnv]
  apply sepWPpLscro_pure_elim; intro hDom
  apply sepWPpLscro_pure_elim; rintro ⟨h_1, h_2, h_3, hbound, hFitGuarded⟩
  have hDomCopy : tlb_ChunkedKeysSampledDom x := hDom
  rcases hDomCopy with ⟨hwt_c, hmsg, pb, restOut, hpb, hbs⟩
  have hwt_ld : x.wt = .lengthDelimited := by
    (cases hwt : x.wt <;> simp [hwt, codecWireTypeToProto] at hwt_c); rfl
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by
    unfold OptPolyEncoderBound at hbound
    rw [hmsg] at hbound
    dsimp [optPolyEncoderPtsLen, optPolyEncoderPolysLen] at hbound
    omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hFit : FitsEnv M lim st (SpqrTightEvs maxOps 384723 2560) :=
    fun evs hevs => hFitGuarded evs (Or.inl ⟨hDom, hevs⟩)
  have hsome_full :
      (mergeMessage CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, restOut) := by
    rw [hwt_c, hmsg, hbs]
    exact proto_mergeMessage_keysSampled_canonical pb restOut hpb
  let cur1 := encodeOptMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pb.sendingHdr ++ restOut
  have hPhase2 : ∀ s1 : State,
      cur1.length ≤ x.bs.length →
      IsDropSuffix x.bs cur1 →
      s1.pc = entry + 168#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 restOut.length →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_304).rebase (blkPl_304).base H) (s0.readReg64 Reg.lr) s1
        (b304OuterPre A lim st s0 s1 x { uc := pb.uc, sendingHdr := none } cur1 (authOps + 4) 42108)
        (WppPost (e2b304_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s1 hcur1_le hcur1_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    have hrestOut_le_cur1 : restOut.length ≤ cur1.length := by
      change restOut.length ≤ (encodeOptMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pb.sendingHdr ++ restOut).length
      conv_rhs => rw [List.length_append]
      exact Nat.le_add_left restOut.length _
    have hrestOut_le : restOut.length ≤ x.bs.length := Nat.le_trans hrestOut_le_cur1 hcur1_le
    have hrestOut_suf : IsDropSuffix x.bs restOut :=
      suffix_trans hcur1_le hcur1_suf hrestOut_le_cur1
        (isDropSuffix_append_right (encodeOptMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pb.sendingHdr) restOut)
    rcases hhdr_opt : pb.sendingHdr with _ | e
    · have hcur1_eq : cur1 = restOut := by
        dsimp only [cur1]; rw [hhdr_opt]; rfl
      have hpb_eq : ({ uc := pb.uc, sendingHdr := none } : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) = pb := by
        cases pb; simp at hhdr_opt; subst hhdr_opt; rfl
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := b304OuterPre A lim st s0 s1 x pb restOut maxOps 384723)
        (by
          dsimp only [b304OuterPre]
          rw [hcur1_eq, hpb_eq]
          exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (b304PoolAt_mono A lim st (by omega) (by decide) s1)))))))
      exact b304_outer_eq_exit hDom hsp_align hsome_full hrestOut_le hrestOut_suf
        hpc1 hrun1 hsp1 htr1 hx21_1 hx22_1 hcs1
    · have he : tlb_ValidPolyEncoderPB e := hpb.2 e hhdr_opt
      let rest2 := tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e) restOut
      have hcur1_eq : cur1 = 0x12#8 :: rest2 := by
        dsimp only [cur1]; rw [hhdr_opt]
        exact encodeOptMessage_tag2_some CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw e restOut
      have hgt2 : restOut.length < cur1.length := by
        rw [hcur1_eq]
        dsimp only [rest2, tlb_lenPrefixed]
        simp only [List.length_cons, List.length_append]
        omega
      have hd2 : decodeVarint cur1 = some (0x12#64, rest2) := by
        rw [hcur1_eq]
        exact codec_decodeVarint_encodeVarint 0x12#64 rest2
      have hrest2_le_cur1 : rest2.length ≤ cur1.length := Nat.le_of_lt (decodeVarint_length hd2)
      have hrest2_le : rest2.length ≤ x.bs.length := Nat.le_trans hrest2_le_cur1 hcur1_le
      have hrest2_suf : IsDropSuffix x.bs rest2 :=
        suffix_trans hcur1_le hcur1_suf hrest2_le_cur1 (decodeVarint_suffix hd2)
      refine b304_outer_step_key_varint hVarintCall hgt2 hsp_align hbs_lt hcur1_le hcur1_suf hd2
        (by decide) (by decide) (by decide)
        (fun s2 hpc2 hrun2 hsp2 htr2 hx8_2 hx1_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2 => ?_)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
      refine b304_outer_tag2_some_step hOps hEncTightCall hFit he hsp_align hbs_lt56
        hrest2_le hrest2_suf
        (fun s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3 => ?_)
        hpc2 hrun2 hsp2 htr2 hx8_2 (by simpa using hx1_2)
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
      have hpb_eq : ({ uc := pb.uc, sendingHdr := some e } : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) = pb := by
        cases pb; simp at hhdr_opt; subst hhdr_opt; rfl
      rw [hpb_eq]
      exact b304_outer_eq_exit hDom hsp_align hsome_full hrestOut_le hrestOut_suf
        hpc3 hrun3 hsp3 htr3 hx21_3 hx22_3 hcs3
  let raw := CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw pb
  let cur0 := raw ++ restOut
  have hraw_len_le : raw.length ≤ 45076 := validChunkedKeysSampledPB_encodeRaw_len_le hpb
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw.length, cur0) := by
    rw [hbs]; exact codec_decodeVarint_tlb_lenPrefixed raw restOut
  have hcur0_le : cur0.length ≤ x.bs.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hcur0_lt : cur0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur0_le hbs_lt
  have hcur0_suf : IsDropSuffix x.bs cur0 := decodeVarint_suffix hdv0
  have hlen_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hnlt_len : ¬ cur0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_toNat]; dsimp only [cur0]; simp only [List.length_append]; omega
  have hule := ule_len_of_ge hnlt_len hcur0_lt
  have hsub := bv_len_sub_limit hnlt_len
  have hlim_eq : cur0.length - raw.length = restOut.length := by
    dsimp only [cur0]; simp only [List.length_append]; omega
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
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3],
        hbs_lt,
        b304_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hcur0_le hcur0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hnil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hnil
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedKeysSampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hcur0_le) (by sep_focus)
      apply SepWP.fold
        (by rw [M.stepEvents_nil]; exact b304PoolAt_init A lim st sm :
          A.pool lim (M.stepEvents [] st) sm ⊢ b304PoolAt A lim st 0 0 sm)
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hcur0_le hcur0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := b304OuterPre A lim st s0 _ x default cur0 0 0)
        (by dsimp only [b304OuterPre, sliceCursorAfter]; rw [hmsg]; sep_entail)
      have hcur0_split : cur0 =
          encodeOptMessage CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw 1#32 pb.uc ++ cur1 := by
        dsimp only [cur0, raw, CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled.encodeRaw, cur1]
        rw [List.append_assoc]
      have hcur1_le_cur0 : cur1.length ≤ cur0.length := by
        rw [hcur0_split]
        conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur1.length _
      have hcur1_le : cur1.length ≤ x.bs.length := Nat.le_trans hcur1_le_cur0 hcur0_le
      have hcur1_suf : IsDropSuffix x.bs cur1 :=
        suffix_trans hcur0_le hcur0_suf hcur1_le_cur0
          (by rw [hcur0_split]; exact isDropSuffix_append_right _ cur1)
      rcases huc_opt : pb.uc with _ | u
      · have hcur0_eq : cur0 = cur1 := by
          rw [hcur0_split, huc_opt]; rfl
        have hm0_eq : (default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) =
            { uc := pb.uc, sendingHdr := none } := by
          rw [huc_opt]; rfl
        refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := b304OuterPre A lim st s0 _ x { uc := pb.uc, sendingHdr := none } cur1
            (authOps + 4) 42108)
          ?_
          (hPhase2 _ hcur1_le hcur1_suf
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm])
            (by simp only [arm64_norm, wp_norm, hx19_m])
            (by simp only [arm64_norm, wp_norm, hx20_m])
            (by simp only [arm64_norm, wp_norm])
            (by simp (config := { failIfUnchanged := false }) only
              [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq])
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩)
        dsimp only [b304OuterPre]
        rw [hcur0_eq, hm0_eq]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (b304PoolAt_mono A lim st (Nat.zero_le _) (Nat.zero_le _) _))))))
      · have hu : tlb_ValidUcHeaderSentPB u := hpb.1 u huc_opt
        let rest1 := tlb_lenPrefixed (CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u) cur1
        have hcur0_eq : cur0 = 0x0a#8 :: rest1 := by
          rw [hcur0_split, huc_opt]
          exact encodeOptMessage_tag1_some CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.HeaderSent.encodeRaw u cur1
        have hgt1 : restOut.length < cur0.length := by
          have hro_le_c1 : restOut.length ≤ cur1.length := by
            change restOut.length ≤ (encodeOptMessage CryptoVerification.LibsignalSpqrV1.PolynomialEncoder.encodeRaw 2#32 pb.sendingHdr ++ restOut).length
            conv_rhs => rw [List.length_append]
            exact Nat.le_add_left restOut.length _
          rw [hcur0_eq]
          dsimp only [rest1, tlb_lenPrefixed]
          simp only [List.length_cons, List.length_append]
          omega
        have hd1 : decodeVarint cur0 = some (0x0a#64, rest1) := by
          rw [hcur0_eq]
          exact codec_decodeVarint_encodeVarint 0x0a#64 rest1
        have hrest1_le_cur0 : rest1.length ≤ cur0.length := Nat.le_of_lt (decodeVarint_length hd1)
        have hrest1_le : rest1.length ≤ x.bs.length := Nat.le_trans hrest1_le_cur0 hcur0_le
        have hrest1_suf : IsDropSuffix x.bs rest1 :=
          suffix_trans hcur0_le hcur0_suf hrest1_le_cur0 (decodeVarint_suffix hd1)
        refine b304_outer_step_key_varint hVarintCall hgt1 hsp_align hbs_lt hcur0_le hcur0_suf hd1
          (by decide) (by decide) (by decide)
          (fun sA hpcA hrunA hspA htrA hx8A hx1A hx19A hx20A hx21A hx22A hx23A hx24A hx25A hcsA => ?_)
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm])
          (by simp (config := { failIfUnchanged := false }) only
            [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        obtain ⟨hx27A, hx28A, hvregsA⟩ := hcsA
        have hx1A' : sA.readReg64 (Reg.gpr 1#5) = 1#64 := by simpa using hx1A
        apply sepWPpLscro_of_vm (mid := entry + 300#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvmA => ?_⟩
          have hdef_ks : (default : CryptoVerification.LibsignalSpqrV1.V1State.Chunked.KeysSampled) = { uc := none, sendingHdr := none } := rfl
          refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
            (P' := b304UcPre A lim st s0 _ x
              (optHeaderSentPBCapAt A.repAlloc x.msgPtr rest1.length none)
              rest1 0 0)
            ?_
            (b304_uc_canonical_placed (outerLimit := restOut.length)
              hVarintCall hBytesCall hAuthTightCall (by omega : authOps + 4 ≤ maxOps)
              hFit hu hsp_align hbs_lt hrest1_le hrest1_suf
              (fun sB hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hcsB => ?_)
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunA])
              (by simp only [arm64_norm, wp_norm, hspA])
              (by simp only [arm64_norm, wp_norm, htrA])
              (by simp only [arm64_norm, wp_norm, hx8A])
              (by simp only [arm64_norm, wp_norm, hx19A])
              (by simp only [arm64_norm, wp_norm, hx20A])
              (by simp only [arm64_norm, wp_norm, hx21A])
              (by simp only [arm64_norm, wp_norm, hx22A])
              (by simp only [arm64_norm, wp_norm, hx23A])
              (by simp only [arm64_norm, wp_norm, hx24A])
              (by simp only [arm64_norm, wp_norm, hx25A])
              ⟨by simp only [arm64_norm, wp_norm, hx27A],
               by simp only [arm64_norm, wp_norm, hx28A],
               by simp only [arm64_norm, wp_norm, hvregsA]⟩)
          · dsimp only [b304OuterPre, b304UcPre]
            rw [hdef_ks]
            dsimp only [chunkedKeysSampledPBCapAt]
            rw [b304PoolAt_eq_of_vmPreserved hvmA]
            exact Entails.of_eq (by sep_ac_rfl)
          · apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
              (P' := b304OuterPre A lim st s0 sB x { uc := pb.uc, sendingHdr := none }
                cur1 (authOps + 4) 42108)
              (by
                dsimp only [b304OuterPre, b304UcPre, chunkedKeysSampledPBCapAt]
                rw [huc_opt]
                exact Entails.of_eq (by sep_ac_rfl))
            exact hPhase2 sB hcur1_le hcur1_suf
              hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hcsB

end DomSteps

/-! ## 4. Exported Guarded-Tight Placed Contracts (`e2b304_`) -/

/-- Block `304` (`V1State.Chunked.KeysSampled::merge`) guarded-tight placed contract,
parametric in `authOps encOps maxOps : Nat` (`hOps : authOps + 4 + encOps ≤ maxOps`), using an
explicit own-block untightened `hFallback` for `¬ tlb_ChunkedKeysSampledDom x`. -/
theorem e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps encOps maxOps : Nat} (hOps : authOps + 4 + encOps ≤ maxOps)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim))) :
    tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim maxOps ext := by
  unfold tlb_ChunkedKeysSampledMergePlacedTightOkOf
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hfr0.1 304 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  by_cases hDom : tlb_ChunkedKeysSampledDom x
  · have hDomOwn := e2b304_own_of_blk_cro (e2b304_dom_blk_ok A lim hOps
      (e2b304_lift_cl_of_own hVarint)
      (e2b304_lift_cro_of_own hBytes)
      (e2b304_lift_cro_of_own hAuthTight)
      (e2b304_lift_cro_of_own hEncTight))
    have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (e2b304_domSpec A lim maxOps)).pre (x, st) s0 ∗ R :=
      Satisfies.of_entails hpre (sepConj_mono_left
        (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _))))
    obtain ⟨sf, hsteps, hout, _⟩ := hDomOwn.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_dom hsp hQL
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  · have hpre_fb : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim)).pre (x, st) s0 ∗ R := by
      refine Satisfies.of_entails hpre (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedKeysSampledMergeSpec,
        chunkedKeysSampledMergeSpecOfEnv]
      refine sepConj_mono_left ?_
      exact Entails.pure_left fun ⟨h0, h1, h2, h3, hFit⟩ =>
        Entails.pure_right ⟨h0, h1, h2, h3, tlb_fitsEnv_fallback_of_not_dom hDom hFit⟩
          (Entails.refl _)
    obtain ⟨sf, hsteps, hout, _⟩ := hFallback.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_fb hsp hQL
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, hp⟩ | ⟨hoom, hp⟩
    · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
      refine Satisfies.of_entails hpost (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedKeysSampledMergeSpec,
        chunkedKeysSampledMergeSpecOfEnv]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      refine Entails.sepExists_elim fun evs => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro evs)
      exact Entails.pure_left fun hevs =>
        Entails.pure_right (Or.inr ⟨hDom, chunkedKeysSampledMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _)
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hp⟩)))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inl ⟨code, hex, hp⟩))))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inr ⟨hoom, hp⟩))))

/-- Block `304` (`V1State.Chunked.KeysSampled::merge`) guarded-tight placed contract,
parametric in `authOps encOps maxOps : Nat` (`hOps : authOps + 4 + encOps ≤ maxOps`), deriving the
`¬ tlb_ChunkedKeysSampledDom x` fallback from `chunked_keys_sampled_merge_cl_placed_ok_of_contracts`. -/
theorem e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps encOps maxOps : Nat} (hOps : authOps + 4 + encOps ≤ maxOps)
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
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext) :
    tlb_ChunkedKeysSampledMergePlacedTightOkOf A lim maxOps ext :=
  e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_fallback A lim hOps hVarint hBytes
    hAuthTight hEncTight
    (e2b304_own_of_blk_cro (chunked_keys_sampled_merge_cl_placed_ok_of_contracts
      (e2b304_lift_cl_of_own hFrom) (e2b304_lift_cl_of_own hPush)
      (e2b304_lift_cl_of_own hVarint) (e2b304_lift_cl_of_own hSkip)
      (e2b304_lift_cro_of_own hBytes) (e2b304_lift_cro_of_own hAuthBase)
      (e2b304_lift_cro_of_own hPolyEncBase)))

/-- Default `2`-op-per-`bytes` instantiation (`authOps = 4`, `encOps = 35`, `maxOps = 43`) of
`e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_fallback`. -/
theorem e2b304_chunkedKeysSampledMerge_placed_tight_ok_default_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOk A lim ext)
    (hEncTight : tlb_PolyEncoderMergePlacedTightOk A lim ext)
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 304 (Rust.withPanics ext))
      (lsmpl.base 304) (withLsCodeRoLoaded lsmpl (chunkedKeysSampledMergeSpec A lim))) :
    tlb_ChunkedKeysSampledMergePlacedTightOk A lim ext :=
  e2b304_chunkedKeysSampledMerge_placed_tight_ok_of_fallback A lim (by decide : 4 + 4 + 35 ≤ 43)
    hVarint hBytes hAuthTight hEncTight hFallback

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304PlacedBudget
