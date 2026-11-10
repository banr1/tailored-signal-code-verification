/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
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
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
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
# Guarded-Tight Placed Budget Proof for `Chunked.HeaderReceived::merge` (Block `306`)

Proves `tlb_ChunkedHeaderReceivedMergePlacedTightOkOf` on Block `306` within
`SpqrTightEvs maxOps 349561 2560` (`authOps + 2 + decOps ≤ maxOps`, default `41 = 4 + 2 + 35`:
inlined `Unchunked.HeaderReceived` `6,946` B + `PolynomialDecoder` `342,615` B) on canonical
`tlb_ChunkedHeaderReceivedDom` inputs, falling back to `ChunkedHeaderReceivedMergeEnv` outside the domain.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB306RPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement instIsLsBlockProg_290 instIsLsBlockProg_291
   instIsLsBlockProg_295 libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecAt vecBuf vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack extract_withLsCodeRoLoaded reserveCap
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix bv32_zeroExtend_ofNat bytesMergeCapOk_zero
   decodeVarint_suffix key_shr32_of_lt key_wt_some pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (encodeBytesField encodeOptMessage encodeUint64Field encodeVarint mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost memRegion_40_cells mergeBytes_length optAuthenticatorPBCapAt
   optAuthenticatorPBCapAt_mono)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderIsCompleteOff protoPolynomialDecoderPadOff
   protoPolynomialDecoderPadSize protoPolynomialDecoderPinnedAt
   protoPolynomialDecoderPolysOff protoPolynomialDecoderPtsNeededOff vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialDecoderPBAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderReceivedMergeGhost ChunkedInl10CalleeSaved OptPolyDecoderBound
   PolyDecoderMergeGhost SepWPpLscro blkPC_306 blkPl_306 bv64_add_zero bv64_sub_zero
   bv_len_sub_limit chunkedHeaderReceivedMerge_fnOff chunkedHeaderReceivedPBCapAt
   chunkedHeaderReceivedPBCapAt_mono chunkedInlBelowStack chunkedInlBelow_authMerge
   chunkedInlBelow_authMerge_entails chunkedInlBelow_bytesMerge3
   chunkedInlBelow_bytesMerge3_entails chunkedInlBelow_decodeVarint2
   chunkedInlBelow_decodeVarint2_entails chunkedInlBelow_eq_polyMerge
   chunkedInlSavedRegs10 chunkedInlStack cmp_len_limit_of_eq cmp_len_limit_of_gt
   codecWireTypeToProto instIsLsBlockProg_296 memRegion_polyDecoder_none_split_inl
   memRegion_unchunked3_none_split optHeaderReceivedPBCapAt optHeaderReceivedPBCapAt_mono
   optPolyDecoderPtsLen optPolynomialDecoderPBAt_some_eq pointsTo64_zero_eq_pointsTo32_pair
   polyDecoderToProto proto_mergeMessage_suffix stackAt_chunkedInl10_epilogue
   stackAt_chunkedInl_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   unchunked3CapAt unchunked3CapAt_eq_hr vecU8CapAt_hr vecU8CapAt_hr_mono withLscroProp
   wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open CryptoVerification.SpqrV1Sync.Codec
  (loopsTo_ch_headerReceived loopsTo_polyDecoder mergeMessage_encode)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedHeaderReceivedDom tlb_ChunkedHeaderReceivedGuardedEnvOf
   tlb_ChunkedHeaderReceivedMergePlacedTightOkOf
   tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf tlb_PolyDecoderMergePlacedTightOkOf
   tlb_ValidAuthPB tlb_ValidChunkedHeaderReceivedPB tlb_ValidPolyDecoderPB
   tlb_ValidUcHeaderReceivedPB tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt
   tlb_domHeap_of_dom tlb_fitsEnv_fallback_of_not_dom tlb_fitsEnv_guarded_of_dom
   tlb_guardedEnv_tight_of_dom tlb_lenPrefixed tlb_polyDecoderMergeTightSpecOfEnv
   tlb_polyDecoderZeroCapAt tlb_polyDecoderZeroCapAt_of_ptr tlb_vecU8ZeroCapAt
   tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget (BytesMerge3EnvCore)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (chunkedHeaderReceivedMergePostEnv_imp_pre chunkedHeaderReceivedMergeSpec
   chunkedHeaderReceivedMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB304Common
  (b304PoolAt b304PoolAt_eq_of_vmPreserved b304PoolAt_init b304PoolAt_mono b304PoolAt_step
   b304PoolAt_step_nil b304_fitsEnv_decodeVarint2_of_some codec_decodeVarint_encodeVarint
   codec_decodeVarint_tlb_lenPrefixed codec_mergeBytes_encode encodeBytesField_tag3_of_ne
   encodeOptMessage_tag1_some encodeOptMessage_tag2_some encodeUint64Field_tag1_of_ne
   isDropSuffix_append_right isDropSuffix_cons_tail proto_mergeMessage_authenticator_canonical)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergePostEnv bytesMerge3RawBudgetSpec polyDecoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderReceivedMerge_fnOff

@[local simp, local arm64_norm]
private theorem e2b306r_bv64_add24_add8 (a : BitVec 64) : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem e2b306r_bv64_add24_add16 (a : BitVec 64) : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem e2b306r_bv64_add24_add24 (a : BitVec 64) : a + 24#64 + 24#64 = a + 48#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem e2b306r_bv64_add24_add32 (a : BitVec 64) : a + 24#64 + 32#64 = a + 56#64 := by bv_omega
@[local simp, local arm64_norm]
private theorem e2b306r_bv64_add24_add40 (a : BitVec 64) : a + 24#64 + 40#64 = a + 64#64 := by bv_omega

private theorem e2b306r_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ## 1. Own-Block ↔ Caller-Block Transfer, Tight Cost, & Zero-Cap Helpers (`e2b306r_`) -/

private class e2b306r_IsLsValidBlock [LibsignalPlacement] (j : Nat) : Prop where
  lt_blocks : j < 624
  not_mutated : (j ∈ libsignalMutatedBlocks) = false
  externs_eq : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns

private instance [LibsignalPlacement] : e2b306r_IsLsValidBlock 290 :=
  ⟨by decide, by decide, (instIsLsBlockProg_290 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b306r_IsLsValidBlock 291 :=
  ⟨by decide, by decide, (instIsLsBlockProg_291 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b306r_IsLsValidBlock 295 :=
  ⟨by decide, by decide, (instIsLsBlockProg_295 (fun _ => none)).externs_eq⟩
private instance [LibsignalPlacement] : e2b306r_IsLsValidBlock 296 :=
  ⟨by decide, by decide, (instIsLsBlockProg_296 (fun _ => none)).externs_eq⟩

private theorem e2b306r_lift_cro_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hj : e2b306r_IsLsValidBlock j] {spec : Spec α}
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

private theorem e2b306r_lift_cl_of_own [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [e2b306r_IsLsValidBlock j] {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j)
      (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok callerProg (lsmpl.base j) (withLsCodeRoLoaded lsmpl spec) :=
  e2b306r_lift_cro_of_own (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee)

private theorem e2b306r_own_of_blk_cro [LibsignalPlacement] {α : Type}
    {blkProg : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg blkProg i H] {spec : Spec α}
    (h : subroutine_ok blkProg (libsignalSessionLib.blockPlacement lsmpl i).base
      (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) (lsmpl.base i)
      (withLsCodeRoLoaded lsmpl spec) := by
  rw [← hprog.eq_blockProgram, ← ls_blockPlacement_base lsmpl i]
  exact h

private theorem e2b306r_fitsEnv_step_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {maxOps ops₁ ops₂ cum₁ cum₂ r₂ : Nat} {evs₁ : List AllocEvent}
    {E₂ : List AllocEvent → Prop}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560))
    (h₁ : SpqrTightEvs ops₁ cum₁ 2560 evs₁)
    (hSub : ∀ evs₂, E₂ evs₂ → SpqrTightEvs ops₂ cum₂ r₂ evs₂)
    (hOps : ops₁ + ops₂ ≤ maxOps)
    (hCum : cum₁ + cum₂ ≤ 349561)
    (hReq : r₂ ≤ 2560) :
    FitsEnv M lim (M.stepEvents evs₁ st) E₂ := by
  intro evs₂ hE₂
  have h₂ := hSub evs₂ hE₂
  have h12 : SpqrTightEvs maxOps 349561 2560 (evs₁ ++ evs₂) :=
    (h₁.append h₂).mono hOps hCum (Nat.max_le.mpr ⟨Nat.le_refl 2560, hReq⟩)
  exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (hFit (evs₁ ++ evs₂) h12)).2

private theorem e2b306r_bytesMerge3Env_spqrTight_64
    {bs v rest : List (BitVec 8)} {evs : List AllocEvent}
    (hm : mergeBytes .lengthDelimited bs = some (v, rest))
    (hv : v.length ≤ 64)
    (hevs : BytesMerge3EnvCore .lengthDelimited 0#64 bs evs) :
    SpqrTightEvs 2 3994 64 evs := by
  change evs = bytesMergeEventsCore .lengthDelimited 0#64 bs at hevs
  subst hevs
  unfold bytesMergeEventsCore
  rw [hm]
  by_cases hz : v.length = 0
  · simp only [hz, ↓reduceIte]
    exact SpqrTightEvs.nil 2 3994 64
  · simp only [hz, ↓reduceIte]
    have hcap0 : (0#64 : BitVec 64).toNat = 0 := rfl
    have hnle : ¬ (v.length ≤ 0) := by omega
    have hres_le : reserveCap 0 0 v.length ≤ 64 := by
      dsimp [reserveCap]
      omega
    have hcost : spqrAllocTightCost 64 = 1997 := by decide
    have h1 : SpqrTightEvs 1 1997 64 (rustAllocEvents v.length 1) := by
      rw [← hcost]
      exact SpqrTightEvs.rustAlloc hv (by decide)
    have h2 : SpqrTightEvs 1 1997 64 (doReserveClearEvents (0#64 : BitVec 64).toNat v.length) := by
      rw [hcap0]
      unfold doReserveClearEvents
      simp only [hnle, ↓reduceIte]
      rw [← hcost]
      exact SpqrTightEvs.rustAlloc hres_le (by decide)
    have h3 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    exact ((h1.append h2).append h3).mono (by decide) (by decide) (by decide)

private theorem e2b306r_mergeMessage_polyDec_canonical (d : PolynomialDecoder)
    (rest : List (BitVec 8)) (hlen : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64) :
    (mergeMessage PolynomialDecoder.mergeField .lengthDelimited default
      (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) rest) 98).toOption = some (d, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw
      default d 98 rest (loopsTo_polyDecoder d hlen) hlen (by decide)]
  rfl

private theorem e2b306r_mergeMessage_top_canonical (pb : V1State.Chunked.HeaderReceived)
    (rest : List (BitVec 8))
    (hlen : (V1State.Chunked.HeaderReceived.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.HeaderReceived.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.HeaderReceived.encodeRaw pb) rest) 99).toOption =
        some (pb, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc,
    mergeMessage_encode V1State.Chunked.HeaderReceived.mergeField 2
      V1State.Chunked.HeaderReceived.encodeRaw default pb 99 rest
      (loopsTo_ch_headerReceived pb hlen) hlen (by decide)]
  rfl

private theorem e2b306r_cells_zero_entails_vecU8At_nil (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ⊢
      vecU8At A a 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  dsimp only [List.length_nil]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, Nat.le_refl,
    true_and, ↓reduceIte, sepConj_emp]
  have hp : (0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := ⟨by decide, by decide⟩
  exact Entails.trans (Entails.pure_right hp (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

private theorem e2b306r_cells_zero_entails_uc_init (A : RustAlloc) (a : BitVec 64) (n : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 32#64) 40 ∗
      ((a + 72#64) ↦₆₄ 0#64) ⊢
      vecU8At A a 0#64 1#64 [] ∗
      optAuthenticatorPBCapAt A (a + 0x18#64) n none ∗
      ((a + 0x48#64) ↦₆₄ 0#64) := by
  dsimp only [optAuthenticatorPBCapAt, noneCap]
  have h1 := e2b306r_cells_zero_entails_vecU8At_nil A a
  have h32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
  rw [h32]
  change _ ⊢
    vecU8At A a 0#64 1#64 [] ∗
    (((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 32#64) 40) ∗
    ((a + 72#64) ↦₆₄ 0#64)
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (Entails.refl _))

private theorem e2b306r_cells_zero_entails_authZeroCapAt (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  have h1 := Entails.trans (e2b306r_cells_zero_entails_vecU8At_nil A a)
    (tlb_vecU8ZeroCapAt_of_ptr A a 1#64 [])
  have h2 := Entails.trans (e2b306r_cells_zero_entails_vecU8At_nil A (a + 24#64))
    (tlb_vecU8ZeroCapAt_of_ptr A (a + 24#64) 1#64 [])
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_omega
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_omega
  rw [h32, h40] at h2
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) []
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

private theorem e2b306r_vecU8At_entails_vecU8CapAt_hr (A : RustAlloc) (a cap ptr : BitVec 64)
    (n : Nat) (bs : List (BitVec 8)) (hcap : BytesMergeCapOk cap n) :
    vecU8At A a cap ptr bs ⊢ vecU8CapAt_hr A a n bs := by
  unfold vecU8CapAt_hr
  refine Entails.trans (Entails.pure_right hcap (Entails.refl _)) ?_
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

private theorem e2b306r_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b306r_default_polyDecoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
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
  have h1 := e2b306r_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
  rw [pointsTo64_zero_eq_pointsTo32_pair (p + 24#64), h28]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

private noncomputable def e2b306r_domSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (maxOps : Nat) : Spec (ChunkedHeaderReceivedMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedHeaderReceivedDom x⌝ ∗
      (chunkedHeaderReceivedMergeSpecOfEnv A lim
        (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps)
        (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps)).pre (x, st) s
  post :=
    (chunkedHeaderReceivedMergeSpecOfEnv A lim
      (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps)
      (tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps)).post

private theorem e2b306r_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (maxOps : Nat) (x : ChunkedHeaderReceivedMergeGhost)
    (s0 s sf : State) (m : V1State.Chunked.HeaderReceived) (cur : List (BitVec 8))
    (evs : List AllocEvent)
    (hDom : tlb_ChunkedHeaderReceivedDom x)
    (hsome : (mergeMessage V1State.Chunked.HeaderReceived.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps 349561 2560 evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) ⊢
      (e2b306r_domSpec A lim maxOps).post (x, st) s0 sf := by
  dsimp only [e2b306r_domSpec, chunkedHeaderReceivedMergeSpecOfEnv]
  rw [hsome, htr, hx0]
  have hPost : tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps x evs := Or.inl ⟨hDom, hevs⟩
  have hPool : A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜tlb_ChunkedHeaderReceivedGuardedEnvOf maxOps x evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf := by
    refine Entails.sepExists_right evs ?_
    exact Entails.pure_right hPost (Entails.of_eq (A.pool_of_vmPreserved hvm).symm)
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono hPool
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

/-! ## 2. Inlined `Unchunked.HeaderReceived` Tight Proof (`+296 → +416 → +168`) -/

private def e2b306r_ucPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (x : ChunkedHeaderReceivedMergeGhost) (msgPart : SepProp)
    (cur : List (BitVec 8)) (ops cum : Nat) : SepProp :=
  msgPart ∗
  optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 80#64) none ∗
  stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
  memRegion (s0.sp - 128#64) 48 ∗
  chunkedInlSavedRegs10 s0.sp s0 ∗
  (x.bufRef ↦₆₄ x.slot) ∗
  sliceCursorAfter x.slot x.ptr x.bs cur ∗
  b304PoolAt A lim st ops cum s

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_306).base

private theorem e2b306r_uc_step_key_varint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {msgPart : SepProp} {cur afterKey : List (BitVec 8)}
    {key : BitVec 64} {outerLimit innerLimit ops cum : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, afterKey))
    (hcont : ∀ s1 : State,
      s1.pc = entry + 436#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = 0#64 →
      s1.readReg64 (Reg.gpr 1#5) = key →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 → s1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s1
        (e2b306r_ucPre A lim st s0 s1 x msgPart afterKey ops cum) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 416#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_ucPre A lim st s0 s x msgPart cur ops cum) Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hafter_le_cur : afterKey.length ≤ cur.length := Nat.le_of_lt (decodeVarint_length hd)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b306r_ucPre, b304PoolAt, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 436#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b306r_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hcur_lt, b304_fitsEnv_decodeVarint2_of_some hd⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 436#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b306r_stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hafter_le_cur) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := e2b306r_ucPre A lim st s0 _ x msgPart afterKey ops cum)
        (by dsimp only [e2b306r_ucPre]; sep_entail)
      exact hcont _
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hpcm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrunm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hspm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htrm, htr])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsm0])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hsm1])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25_m])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27_m],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28_m],
         by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b306r_uc_field1_epoch [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {cur1 : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_cur1 : innerLimit ≤ cur1.length)
    (hcur0_le : (encodeUint64Field 1#32 epoch ++ cur1).length ≤ x.bs.length)
    (hcur0_suf : IsDropSuffix x.bs (encodeUint64Field 1#32 epoch ++ cur1))
    (hcont : ∀ s' : State,
      s'.pc = entry + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_ucPre A lim st s0 s' x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) cur1.length none ∗
            ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
          cur1 0 0) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 416#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_ucPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64)
            (encodeUint64Field 1#32 epoch ++ cur1).length none ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ 0#64))
        (encodeUint64Field 1#32 epoch ++ cur1) 0 0) Q (WppPanicFalse R) := by
  by_cases hep : epoch = 0#64
  · subst hep
    have hf1 : encodeUint64Field 1#32 0#64 = [] := by decide
    rw [hf1, List.nil_append]
    exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hcur0_eq := encodeUint64Field_tag1_of_ne epoch hep cur1
    rw [hcur0_eq] at hcur0_le hcur0_suf ⊢
    let afterKey := encodeVarint epoch ++ cur1
    have hgt_lim : ¬ (0x08#8 :: afterKey).length ≤ innerLimit := by
      dsimp only [afterKey]; simp only [List.length_cons, List.length_append]; omega
    have hcur0_lt : (0x08#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur0_le hbs_lt
    have hk_eq : (0x08#8 :: afterKey) = encodeVarint 0x08#64 ++ afterKey := by
      have : encodeVarint 0x08#64 = [0x08#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x08#8 :: afterKey) = some (0x08#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x08#64 afterKey
    refine e2b306r_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur0_le hcur0_lt hcur0_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur0 : afterKey.length ≤ (0x08#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur0 hcur0_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur0_le hcur0_suf hafter_le_cur0 (isDropSuffix_cons_tail 0x08#8 afterKey)
    have hd_val : decodeVarint afterKey = some (epoch, cur1) :=
      codec_decodeVarint_encodeVarint epoch cur1
    have hcur1_le_after : cur1.length ≤ afterKey.length := Nat.le_of_lt (decodeVarint_length hd_val)
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b306r_ucPre, b304PoolAt, sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, afterPtr, afterKey⟩, M.stepEvents evs st))
        (ret_pc := entry + 568#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, e2b306r_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_1], hafter_lt, b304_fitsEnv_decodeVarint2_of_some hd_val⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
          e2b306r_stackAt_decodeVarint2_raw_eq, hd_val, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_dv
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hcur1_le_after) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step_nil A lim st (VmPreserved.refl sm) hevs
            (decodeVarint2Env_eq_nil_of_some hd_val hevs_dv))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := e2b306r_ucPre A lim st s0 _ x
            (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) cur1.length none ∗
              ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
            cur1 0 0)
          (by dsimp only [e2b306r_ucPre, optAuthenticatorPBCapAt]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hrunm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hspm])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, htrm, htr1])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx19_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx20_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx21_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx22_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx23_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx24_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx25_m])
          (by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx27_m],
           by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hx28_m],
           by simp (config := { failIfUnchanged := false }) only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b306r_uc_field2_auth [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hOps_uc : authOps + 2 ≤ maxOps)
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {cur2 : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560))
    (hauth_valid : ∀ a, auth = some a → tlb_ValidAuthPB a)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hlim_le_cur2 : innerLimit ≤ cur2.length)
    (hcur1_le : (encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2).length ≤ x.bs.length)
    (hcur1_suf : IsDropSuffix x.bs (encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2))
    (hcont : ∀ s' : State,
      s'.pc = entry + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_ucPre A lim st s0 s' x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) cur2.length auth ∗
            ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
          cur2 authOps 2952) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 416#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_ucPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64)
            (encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2).length none ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
        (encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 auth ++ cur2) 0 0)
      Q (WppPanicFalse R) := by
  rcases auth with _ | a
  · dsimp only [encodeOptMessage, List.nil_append]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := e2b306r_ucPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) cur2.length none ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
        cur2 authOps 2952)
    · dsimp only [e2b306r_ucPre]
      have hm := b304PoolAt_mono A lim st (Nat.zero_le authOps) (by decide : 0 ≤ 2952) s
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm))))))
    · exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have ha : tlb_ValidAuthPB a := hauth_valid a rfl
    have hcur1_eq := encodeOptMessage_tag2_some ProtoAuthenticator.encodeRaw a cur2
    rw [hcur1_eq] at hcur1_le hcur1_suf ⊢
    let afterKey := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw a) cur2
    have hgt_lim : ¬ (0x12#8 :: afterKey).length ≤ innerLimit := by
      dsimp only [afterKey, tlb_lenPrefixed]
      simp only [List.length_cons, List.length_append]
      omega
    have hcur1_lt : (0x12#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur1_le hbs_lt
    have hk_eq : (0x12#8 :: afterKey) = encodeVarint 0x12#64 ++ afterKey := by
      have : encodeVarint 0x12#64 = [0x12#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x12#8 :: afterKey) = some (0x12#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x12#64 afterKey
    refine e2b306r_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur1_le hcur1_lt hcur1_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur1 : afterKey.length ≤ (0x12#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur1 hcur1_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur1_le hcur1_suf hafter_le_cur1 (isDropSuffix_cons_tail 0x12#8 afterKey)
    have hcur2_le_after : cur2.length ≤ afterKey.length := by
      dsimp only [afterKey, tlb_lenPrefixed]; simp only [List.length_append]; omega
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    let x_auth : AuthMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr + 0x18#64, default, x.bufRef, x.slot, afterPtr, afterKey⟩
    have hAuthDom : tlb_AuthDom x_auth := ⟨rfl, rfl, a, cur2, ha, rfl⟩
    have hauth_res :
        (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x_auth.wt)
          x_auth.msg x_auth.bs 97).toOption = some (a, cur2) :=
      proto_mergeMessage_authenticator_canonical a cur2 ha
    apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
    by_vm_steps
      (conv => arg 4; rw [e2b306r_ucPre, b304PoolAt, optAuthenticatorPBCapAt,
        memRegion_40_cells (x.msgPtr + 0x18#64), sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_authMerge s0.sp])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
      apply SepWP.exists_elim; intro evs; apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4; apply SepWP.exists_elim; intro w5
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.fold (e2b306r_cells_zero_entails_authZeroCapAt A.repAlloc (x.msgPtr + 0x18#64)) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_auth, M.stepEvents evs st))
        (ret_pc := entry + 548#64) hAuthTightCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [tlb_authMergeTightSpecOfEnv, x_auth]
              rw [tlb_domHeap_of_dom hAuthDom]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hafter_lt,
          tlb_fitsEnv_guarded_of_dom hAuthDom
            (e2b306r_fitsEnv_step_tight hFit hevs (fun _ h => h)
              (by omega : 0 + authOps ≤ maxOps) (by decide : 0 + 2952 ≤ 349561) (by decide : 32 ≤ 2560))⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv, x_auth,
          hauth_res, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_a
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_g
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hevs_a : SpqrTightEvs authOps 2952 32 evs_a :=
          tlb_guardedEnv_tight_of_dom hAuthDom hevs_g
        apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hcur2_le_after) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step A lim st (VmPreserved.refl sm) hevs hevs_a (by decide : 32 ≤ 2560))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := e2b306r_ucPre A lim st s0 _ x
            (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
              optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) cur2.length (some a) ∗
              ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
            cur2 authOps 2952)
          (by dsimp only [e2b306r_ucPre, optAuthenticatorPBCapAt]; simp only [Nat.zero_add, arm64_norm]; sep_entail)
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

private theorem e2b306r_uc_field3_hdr [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hOps_uc : authOps + 2 ≤ maxOps)
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {hdr restAfterUc : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560))
    (hhdr_len : hdr.length ≤ 64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur2_le : (encodeBytesField 3#32 hdr ++ restAfterUc).length ≤ x.bs.length)
    (hcur2_suf : IsDropSuffix x.bs (encodeBytesField 3#32 hdr ++ restAfterUc))
    (hcont : ∀ s' : State,
      s'.pc = entry + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 restAfterUc.length →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_ucPre A lim st s0 s' x
          (unchunked3CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth hdr)
          restAfterUc (authOps + 2) 6946) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 416#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 restAfterUc.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_ucPre A lim st s0 s x
        (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
          optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64)
            (encodeBytesField 3#32 hdr ++ restAfterUc).length auth ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ epoch))
        (encodeBytesField 3#32 hdr ++ restAfterUc) authOps 2952) Q (WppPanicFalse R) := by
  by_cases hhdr_nil : hdr = []
  · subst hhdr_nil
    have hf3 : encodeBytesField 3#32 [] = [] := by decide
    rw [hf3, List.nil_append]
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := e2b306r_ucPre A lim st s0 s x
        (unchunked3CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth [])
        restAfterUc (authOps + 2) 6946)
    · dsimp only [e2b306r_ucPre]
      rw [unchunked3CapAt_eq_hr]
      have hcap := e2b306r_vecU8At_entails_vecU8CapAt_hr A.repAlloc x.msgPtr 0#64 1#64
        restAfterUc.length [] bytesMergeCapOk_zero
      have hm := b304PoolAt_mono A lim st (by omega : authOps ≤ authOps + 2) (by decide : 2952 ≤ 6946) s
      exact sepConj_mono (sepConj_mono_left hcap)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hm))))))
    · exact hcont s hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  · have hcur2_eq := encodeBytesField_tag3_of_ne hdr restAfterUc hhdr_nil
    rw [hcur2_eq] at hcur2_le hcur2_suf ⊢
    let afterKey := encodeVarint (BitVec.ofNat 64 hdr.length) ++ hdr ++ restAfterUc
    have hgt_lim : ¬ (0x1a#8 :: afterKey).length ≤ restAfterUc.length := by
      dsimp only [afterKey]; simp only [List.length_cons, List.length_append]; omega
    have hcur2_lt : (0x1a#8 :: afterKey).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur2_le hbs_lt
    have hk_eq : (0x1a#8 :: afterKey) = encodeVarint 0x1a#64 ++ afterKey := by
      have : encodeVarint 0x1a#64 = [0x1a#8] := by decide
      rw [this]; rfl
    have hd_key : decodeVarint (0x1a#8 :: afterKey) = some (0x1a#64, afterKey) := by
      rw [hk_eq]; exact codec_decodeVarint_encodeVarint 0x1a#64 afterKey
    refine e2b306r_uc_step_key_varint hVarintCall hgt_lim hsp_align hcur2_le hcur2_lt hcur2_suf hd_key
      ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hcs1
    obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
    have hafter_le_cur2 : afterKey.length ≤ (0x1a#8 :: afterKey).length := by simp
    have hafter_le : afterKey.length ≤ x.bs.length := Nat.le_trans hafter_le_cur2 hcur2_le
    have hafter_lt : afterKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hafter_le hbs_lt
    have hafter_suf : IsDropSuffix x.bs afterKey :=
      suffix_trans hcur2_le hcur2_suf hafter_le_cur2 (isDropSuffix_cons_tail 0x1a#8 afterKey)
    have hmb : mergeBytes .lengthDelimited afterKey = some (hdr, restAfterUc) :=
      codec_mergeBytes_encode hdr restAfterUc (by omega)
    have hrest_le_after : restAfterUc.length ≤ afterKey.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hrest_le_cur2 : restAfterUc.length ≤ (0x1a#8 :: afterKey).length :=
      Nat.le_trans hrest_le_after hafter_le_cur2
    let afterPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - afterKey.length)
    let x_bm : BytesMergeGhost :=
      ⟨.lengthDelimited, x.msgPtr, 0#64, 1#64, [], x.bufRef, x.slot, afterPtr, afterKey⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [e2b306r_ucPre, b304PoolAt, sliceCursorAfter_eq_split hafter_le hafter_suf,
        chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
        (ret_pc := entry + 404#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hafter_lt,
          bytesMergeCapOk_zero,
          e2b306r_fitsEnv_step_tight hFit hevs
            (fun _ hb => e2b306r_bytesMerge3Env_spqrTight_64 hmb hhdr_len hb)
            (by omega : authOps + 2 ≤ maxOps) (by decide : 2952 + 3994 ≤ 349561) (by decide : 64 ≤ 2560)⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_b
        apply SepWP.exists_elim; intro cap'
        apply SepWP.exists_elim; intro ptr'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_b
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hafter_le hafter_suf hrest_le_after) (by sep_focus)
        apply SepWP.fold
          (e2b306r_vecU8At_entails_vecU8CapAt_hr A.repAlloc x.msgPtr cap' ptr'
            restAfterUc.length hdr hcap') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) auth hrest_le_cur2) (by sep_focus)
        apply SepWP.fold
          (b304PoolAt_step A lim st (VmPreserved.refl sm) hevs
            (e2b306r_bytesMerge3Env_spqrTight_64 hmb hhdr_len hevs_b) (by decide : 64 ≤ 2560))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← b304PoolAt_eq_of_vmPreserved hvm2]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := e2b306r_ucPre A lim st s0 _ x
            (unchunked3CapAt A.repAlloc x.msgPtr restAfterUc.length epoch auth hdr)
            restAfterUc (authOps + 2) 6946)
          (by dsimp only [e2b306r_ucPre]; rw [unchunked3CapAt_eq_hr]; simp only [Nat.reduceAdd, arm64_norm]; sep_entail)
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

private theorem e2b306r_uc_canonical_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps maxOps : Nat} {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hOps_uc : authOps + 2 ≤ maxOps)
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {u : V1State.Unchunked.HeaderReceived} {restAfterUc : List (BitVec 8)}
    {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560))
    (hu : tlb_ValidUcHeaderReceivedPB u)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : (tlb_lenPrefixed (V1State.Unchunked.HeaderReceived.encodeRaw u) restAfterUc).length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (V1State.Unchunked.HeaderReceived.encodeRaw u) restAfterUc))
    (hcont : ∀ s' : State,
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_ucPre A lim st s0 s' x
          (optHeaderReceivedPBCapAt A.repAlloc x.msgPtr restAfterUc.length (some u))
          restAfterUc (authOps + 2) 6946) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 296#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = 2#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_ucPre A lim st s0 s x
        (optHeaderReceivedPBCapAt A.repAlloc x.msgPtr
          (tlb_lenPrefixed (V1State.Unchunked.HeaderReceived.encodeRaw u) restAfterUc).length none)
        (tlb_lenPrefixed (V1State.Unchunked.HeaderReceived.encodeRaw u) restAfterUc) 0 0)
      Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let raw := V1State.Unchunked.HeaderReceived.encodeRaw u
  let rest := tlb_lenPrefixed raw restAfterUc
  let cur0 := raw ++ restAfterUc
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  have hraw_lt : raw.length < 2 ^ 64 := by
    have : raw.length ≤ rest.length := by
      dsimp only [rest, tlb_lenPrefixed]; simp only [List.length_append]; omega
    omega
  have hdv0 : decodeVarint rest = some (BitVec.ofNat 64 raw.length, cur0) :=
    codec_decodeVarint_tlb_lenPrefixed raw restAfterUc
  have hcur0_le_rest : cur0.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv0)
  have hcur0_le : cur0.length ≤ x.bs.length := Nat.le_trans hcur0_le_rest hrest_le
  have hcur0_lt : cur0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur0_le hbs_lt
  have hcur0_suf : IsDropSuffix x.bs cur0 :=
    suffix_trans hrest_le hrest_suf hcur0_le_rest (decodeVarint_suffix hdv0)
  have hlen_toNat : (BitVec.ofNat 64 raw.length).toNat = raw.length := by
    simp only [BitVec.toNat_ofNat]; omega
  have hnlt_len : ¬ cur0.length < (BitVec.ofNat 64 raw.length).toNat := by
    rw [hlen_toNat]; dsimp only [cur0]; simp only [List.length_append]; omega
  have hule := ule_len_of_ge hnlt_len hcur0_lt
  have hsub := bv_len_sub_limit hnlt_len
  have hlim_eq : cur0.length - raw.length = restAfterUc.length := by
    dsimp only [cur0]; simp only [List.length_append]; omega
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b306r_ucPre, b304PoolAt, optHeaderReceivedPBCapAt,
      memRegion_unchunked3_none_split x.msgPtr,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, sepConj_pure_left_comm, arm64_norm])
    apply SepWP.exists_elim; intro evs; apply SepWP.exists_elim; intro v72
    apply SepWP.exists_elim; intro v24; apply SepWP.exists_elim; intro v16
    apply SepWP.exists_elim; intro v8
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.fold (e2b306r_cells_zero_entails_uc_init A.repAlloc x.msgPtr cur0.length) (by sep_focus)
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
            simp only [A.pool_of_vmPreserved hvm1, e2b306r_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19], hrest_lt, b304_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    apply sepWPpLscro_of_vm (mid := entry + 416#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b306r_stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hcur0_le_rest) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
        (by sep_focus)
      (conv => arg 4; rw [sliceCursorAfter_eq_split hcur0_le hcur0_suf, sliceCursorAt]; simp only [sepConj_assoc])
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hcur0_le hcur0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      let f1 := encodeUint64Field 1#32 u.epoch
      let f2 := encodeOptMessage ProtoAuthenticator.encodeRaw 2#32 u.auth
      let f3 := encodeBytesField 3#32 u.hdr
      let cur2 := f3 ++ restAfterUc
      let cur1 := f2 ++ cur2
      have hcur0_split : cur0 = f1 ++ cur1 := by
        dsimp only [cur0, raw, V1State.Unchunked.HeaderReceived.encodeRaw, f1, f2, f3, cur1, cur2]
        simp only [List.append_assoc]
      have hcur1_le_cur0 : cur1.length ≤ cur0.length := by
        rw [hcur0_split]; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur1.length f1.length
      have hcur1_le : cur1.length ≤ x.bs.length := Nat.le_trans hcur1_le_cur0 hcur0_le
      have hcur1_suf : IsDropSuffix x.bs cur1 :=
        suffix_trans hcur0_le hcur0_suf hcur1_le_cur0 (by rw [hcur0_split]; exact isDropSuffix_append_right f1 cur1)
      have hcur2_le_cur1 : cur2.length ≤ cur1.length := by
        change cur2.length ≤ (f2 ++ cur2).length; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left cur2.length f2.length
      have hcur2_le : cur2.length ≤ x.bs.length := Nat.le_trans hcur2_le_cur1 hcur1_le
      have hcur2_suf : IsDropSuffix x.bs cur2 :=
        suffix_trans hcur1_le hcur1_suf hcur2_le_cur1 (isDropSuffix_append_right f2 cur2)
      have hend_le_cur2 : restAfterUc.length ≤ cur2.length := by
        change restAfterUc.length ≤ (f3 ++ restAfterUc).length; conv_rhs => rw [List.length_append]
        exact Nat.le_add_left restAfterUc.length f3.length
      have hend_le : restAfterUc.length ≤ x.bs.length := Nat.le_trans hend_le_cur2 hcur2_le
      have hend_suf : IsDropSuffix x.bs restAfterUc :=
        suffix_trans hcur2_le hcur2_suf hend_le_cur2 (isDropSuffix_append_right f3 restAfterUc)
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := e2b306r_ucPre A lim st s0 _ x
          (vecU8At A.repAlloc x.msgPtr 0#64 1#64 [] ∗
            optAuthenticatorPBCapAt A.repAlloc (x.msgPtr + 0x18#64) (f1 ++ cur1).length none ∗
            ((x.msgPtr + 0x48#64) ↦₆₄ 0#64))
          (f1 ++ cur1) 0 0)
        (by rw [← hcur0_split]; dsimp only [e2b306r_ucPre, sliceCursorAfter]; sep_entail)
      refine e2b306r_uc_field1_epoch (outerLimit := outerLimit) (innerLimit := restAfterUc.length)
        hVarintCall hsp_align hbs_lt
        (Nat.le_trans hend_le_cur2 hcur2_le_cur1)
        (by rw [← hcur0_split]; exact hcur0_le)
        (by rw [← hcur0_split]; exact hcur0_suf)
        (fun sA hpcA hrunA hspA htrA hx19A hx20A hx21A hx22A hx23A hx24A hx25A hx26A hcsA => ?_)
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
        (by simp only [arm64_norm, wp_norm, hsm1, hsub, hlen_toNat, hlim_eq])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      refine e2b306r_uc_field2_auth hVarintCall hAuthTightCall hOps_uc hFit hu.1 hsp_align hbs_lt
        hend_le_cur2 hcur1_le hcur1_suf
        (fun sB hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hx26B hcsB => ?_)
        hpcA hrunA hspA htrA hx19A hx20A hx21A hx22A hx23A hx24A hx25A hx26A hcsA
      refine e2b306r_uc_field3_hdr hVarintCall hBytesCall hOps_uc hFit hu.2
        hsp_align hbs_lt hcur2_le hcur2_suf
        (fun sC hpcC hrunC hspC htrC hx19C hx20C hx21C hx22C hx23C hx24C hx25C hx26C hcsC => ?_)
        hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hx26B hcsB
      obtain ⟨hx27C, hx28C, hvregsC⟩ := hcsC
      obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : restAfterUc.length = restAfterUc.length)
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; rw [e2b306r_ucPre, sliceCursorAfter_eq_split hend_le hend_suf, sliceCursorAt])
        (conv => arg 4; simp only [sepConj_assoc])
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hend_le hend_suf) (by sep_focus)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := e2b306r_ucPre A lim st s0 _ x
            (optHeaderReceivedPBCapAt A.repAlloc x.msgPtr restAfterUc.length (some u))
            restAfterUc (authOps + 2) 6946)
          (by dsimp only [e2b306r_ucPre, optHeaderReceivedPBCapAt, sliceCursorAfter];
              rw [b304PoolAt_eq_of_vmPreserved hvm3]; simp only [arm64_norm]; sep_entail)
        exact hcont _
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunC])
          (by simp only [arm64_norm, wp_norm, hspC])
          (by simp only [arm64_norm, wp_norm, htrC])
          (by simp only [arm64_norm, wp_norm, hx19C])
          (by simp only [arm64_norm, wp_norm, hx20C])
          (by simp only [arm64_norm, wp_norm, hx21C])
          (by simp only [arm64_norm, wp_norm, hx22C])
          (by simp only [arm64_norm, wp_norm, hx23C])
          (by simp only [arm64_norm, wp_norm, hx24C])
          (by simp only [arm64_norm, wp_norm, hx25C])
          ⟨by simp only [arm64_norm, wp_norm, hx27C],
           by simp only [arm64_norm, wp_norm, hx28C],
           by simp only [arm64_norm, wp_norm, hvregsC]⟩

/-! ## 3. Canonical Outer Loop Steps (`+168 → +228`, Tag `2` `receivingEk`, `+168 → ret`) -/

private def e2b306r_outerPre {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 s : State) (x : ChunkedHeaderReceivedMergeGhost)
    (m : V1State.Chunked.HeaderReceived) (cur : List (BitVec 8)) (ops cum : Nat) : SepProp :=
  chunkedHeaderReceivedPBCapAt A.repAlloc x.msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
    sliceCursorAfter x.slot x.ptr x.bs cur ∗
    b304PoolAt A lim st ops cum s

private theorem e2b306r_outer_step_key_varint [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {m : V1State.Chunked.HeaderReceived} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {outerLimit ops cum : Nat}
    (hgt_lim : outerLimit < cur.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_lt : key.toNat < 2 ^ 32)
    (hwt : WireType.ofNat? (key.toNat % 8) = some .lengthDelimited)
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
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_outerPre A lim st s0 s' x m rest ops cum) Q (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_outerPre A lim st s0 s x m cur ops cum) Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
  have hnle_lim : ¬ cur.length ≤ outerLimit := by omega
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hnle_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b306r_outerPre, b304PoolAt,
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
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, e2b306r_stackAt_decodeVarint2_raw_eq,
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
        e2b306r_stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedHeaderReceivedPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (b304PoolAt_step_nil A lim st (VmPreserved.refl sm) hevs
          (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm2]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := e2b306r_outerPre A lim st s0 _ x m rest ops cum)
        (by dsimp only [e2b306r_outerPre]; sep_entail)
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

private theorem e2b306r_outer_tag2_some_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps decOps maxOps : Nat} {H : String → Option (State → State)}
    (hOps : authOps + 2 + decOps ≤ maxOps)
    (hDecTightCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps))))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {Q : State → SepProp → Prop} {R : SepProp}
    {s0 s : State} {ucOpt : Option V1State.Unchunked.HeaderReceived}
    {d : PolynomialDecoder} {restOut : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560))
    (hd : tlb_ValidPolyDecoderPB d)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hrest_le : (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) restOut).length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) restOut))
    (hcont : ∀ s' : State,
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 restOut.length →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (e2b306r_outerPre A lim st s0 s' x { uc := ucOpt, receivingEk := some d }
          restOut maxOps 349561) Q (WppPanicFalse R))
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
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_outerPre A lim st s0 s x { uc := ucOpt, receivingEk := none }
        (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) restOut) (authOps + 2) 6946)
      Q (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let rest := tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) restOut
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyDecoderMergeGhost :=
    ⟨.lengthDelimited, x.msgPtr + 80#64, default, x.bufRef, x.slot, restPtr, rest⟩
  have hPolyDom : tlb_PolyDecoderDom x_poly := ⟨rfl, rfl, d, restOut, hd, rfl⟩
  have hd_lt : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64 := by
    have h1 : (PolynomialDecoder.encodeRaw d).length ≤ rest.length := by
      dsimp only [rest, tlb_lenPrefixed]; simp only [List.length_append]; omega
    have h2 : rest.length ≤ x.bs.length := hrest_le
    omega
  have hpoly_res :
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto (.lengthDelimited : WireType)) default rest 98).toOption =
        some (d, restOut) :=
    e2b306r_mergeMessage_polyDec_canonical d restOut hd_lt
  have hrestOut_le : restOut.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
  apply sepWPpLscro_of_vm (mid := entry + 244#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
      (P' := e2b306r_outerPre A lim st s0 _ x { uc := ucOpt, receivingEk := none } rest (authOps + 2) 6946)
      (by dsimp only [e2b306r_outerPre]; rw [b304PoolAt_eq_of_vmPreserved hvm0]; exact Entails.refl _)
    apply sepWPpLscro_of_vm (mid := entry + 268#64)
    by_vm_steps
      (conv => arg 4; rw [e2b306r_outerPre, chunkedHeaderReceivedPBCapAt,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl (x.msgPtr + 80#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro b32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := e2b306r_default_polyDecoder_entails_zeroCap A.repAlloc (x.msgPtr + 80#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← b304PoolAt_eq_of_vmPreserved hvm1]
      apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
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
            (tlb_PolyDecoderGuardedEnvOf decOps x_poly) :=
          tlb_fitsEnv_guarded_of_dom hPolyDom
            (e2b306r_fitsEnv_step_tight hFit hevs (fun _ h => h) hOps
              (by decide : 6946 + 342615 ≤ 349561) (Nat.le_refl 2560))
        have hpts_bound : x_poly.msg.pts.length + x_poly.bs.length < 2 ^ 56 := by
          have h0 : (default : PolynomialDecoder).pts.length = 0 := rfl
          dsimp only [x_poly, rest]; rw [h0]; omega
        refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
          (ret_pc := entry + 284#64) hDecTightCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_polyDecoderMergeTightSpecOfEnv, x_poly]
                rw [tlb_domHeap_of_dom hPolyDom]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, arm64_norm, wp_norm, hsp])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx8],
            by simp only [arm64_norm, wp_norm, hx20],
            by simp only [arm64_norm, wp_norm, hx19],
            hpts_bound,
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
          (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv, polyDecoderMergeSpecOfEnv,
            PolyDecoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_p
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_g
          wp_focus_pure; intro hsm0
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
          have hevs_p : SpqrTightEvs decOps 342615 2560 evs_p :=
            tlb_guardedEnv_tight_of_dom hPolyDom hevs_g
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrestOut_le)
            (by dsimp only [rest]; sep_focus)
          apply SepWP.fold (optHeaderReceivedPBCapAt_mono A.repAlloc x.msgPtr ucOpt hrestOut_le)
            (by dsimp only [rest]; sep_focus)
          apply SepWP.fold
            (Entails.trans
              (b304PoolAt_step A lim st (VmPreserved.refl sm) hevs hevs_p (Nat.le_refl 2560))
              (b304PoolAt_mono A lim st hOps (by decide : 6946 + 342615 ≤ 349561) sm))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← b304PoolAt_eq_of_vmPreserved hvm3]
          apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
            (P' := e2b306r_outerPre A lim st s0 _ x { uc := ucOpt, receivingEk := some d }
              restOut maxOps 349561)
            (by dsimp only [e2b306r_outerPre, chunkedHeaderReceivedPBCapAt];
                rw [optPolynomialDecoderPBAt_some_eq]; simp only [arm64_norm]; sep_entail)
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

private theorem e2b306r_outer_eq_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {maxOps : Nat} {H : String → Option (State → State)}
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp}
    {s0 s : State} {m : V1State.Chunked.HeaderReceived} {cur : List (BitVec 8)}
    (hDom : tlb_ChunkedHeaderReceivedDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsome : (mergeMessage V1State.Chunked.HeaderReceived.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hcur_le : cur.length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 cur.length)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (e2b306r_outerPre A lim st s0 s x m cur maxOps 349561)
      (WppPost (e2b306r_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : cur.length = cur.length)
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b306r_outerPre, b304PoolAt,
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
      (e2b306r_ok_exit_entails A lim st maxOps x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b306r_dom_blk_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {authOps decOps maxOps : Nat} (hOps : authOps + 2 + decOps ≤ maxOps)
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf authOps) (tlb_AuthGuardedEnvOf authOps))))
    (hDecTightCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_PolyDecoderGuardedEnvOf decOps) (tlb_PolyDecoderGuardedEnvOf decOps)))) :
    subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (blkPl_306).base
      (withLsCodeRoLoaded lsmpl (e2b306r_domSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b306r_domSpec chunkedHeaderReceivedMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b306r_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R)
  dsimp only [e2b306r_domSpec, chunkedHeaderReceivedMergeSpecOfEnv]
  apply sepWPpLscro_pure_elim; intro hDom
  apply sepWPpLscro_pure_elim; rintro ⟨h_1, h_2, h_3, hbound, hFitGuarded⟩
  have hDomCopy : tlb_ChunkedHeaderReceivedDom x := hDom
  rcases hDomCopy with ⟨hwt_c, hmsg, pb, restOut, hpb, hbs⟩
  have hwt_ld : x.wt = .lengthDelimited := by
    (cases hwt : x.wt <;> simp [hwt, codecWireTypeToProto] at hwt_c); rfl
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by
    unfold OptPolyDecoderBound at hbound
    rw [hmsg] at hbound
    dsimp [optPolyDecoderPtsLen] at hbound
    omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hFit : FitsEnv M lim st (SpqrTightEvs maxOps 349561 2560) :=
    fun evs hevs => hFitGuarded evs (Or.inl ⟨hDom, hevs⟩)
  let raw := V1State.Chunked.HeaderReceived.encodeRaw pb
  have hraw_lt : raw.length < 2 ^ 64 := by
    have : raw.length ≤ x.bs.length := by
      rw [hbs]; dsimp only [raw, tlb_lenPrefixed]; simp only [List.length_append]; omega
    omega
  have hsome_full :
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, restOut) := by
    rw [hwt_c, hmsg, hbs]
    exact e2b306r_mergeMessage_top_canonical pb restOut hraw_lt
  let cur1 := encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ restOut
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
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s1
        (e2b306r_outerPre A lim st s0 s1 x { uc := pb.uc, receivingEk := none } cur1 (authOps + 2) 6946)
        (WppPost (e2b306r_domSpec A lim maxOps) (x, st) R s0) (WppPanicFalse R) := by
    intro s1 hcur1_le hcur1_suf hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    have hrestOut_le_cur1 : restOut.length ≤ cur1.length := by
      change restOut.length ≤ (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ restOut).length
      conv_rhs => rw [List.length_append]
      exact Nat.le_add_left restOut.length _
    have hrestOut_le : restOut.length ≤ x.bs.length := Nat.le_trans hrestOut_le_cur1 hcur1_le
    have hrestOut_suf : IsDropSuffix x.bs restOut :=
      suffix_trans hcur1_le hcur1_suf hrestOut_le_cur1
        (isDropSuffix_append_right (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk) restOut)
    rcases hek_opt : pb.receivingEk with _ | d
    · have hcur1_eq : cur1 = restOut := by
        dsimp only [cur1]; rw [hek_opt]; rfl
      have hpb_eq : ({ uc := pb.uc, receivingEk := none } : V1State.Chunked.HeaderReceived) = pb := by
        cases pb; simp at hek_opt; subst hek_opt; rfl
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
        (P' := e2b306r_outerPre A lim st s0 s1 x pb restOut maxOps 349561)
        (by
          dsimp only [e2b306r_outerPre]
          rw [hcur1_eq, hpb_eq]
          exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (b304PoolAt_mono A lim st (by omega) (by decide) s1)))))))
      exact e2b306r_outer_eq_exit hDom hsp_align hsome_full hrestOut_le hrestOut_suf
        hpc1 hrun1 hsp1 htr1 hx21_1 hx22_1 hcs1
    · have hd : tlb_ValidPolyDecoderPB d := hpb.2 d hek_opt
      let rest2 := tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) restOut
      have hcur1_eq : cur1 = 0x12#8 :: rest2 := by
        dsimp only [cur1]; rw [hek_opt]
        exact encodeOptMessage_tag2_some PolynomialDecoder.encodeRaw d restOut
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
      refine e2b306r_outer_step_key_varint hVarintCall hgt2 hsp_align hbs_lt hcur1_le hcur1_suf hd2
        (by decide) (by decide) (by decide)
        (fun s2 hpc2 hrun2 hsp2 htr2 hx8_2 hx1_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2 => ?_)
        hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
      refine e2b306r_outer_tag2_some_step hOps hDecTightCall hFit hd hsp_align hbs_lt56
        hrest2_le hrest2_suf
        (fun s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3 => ?_)
        hpc2 hrun2 hsp2 htr2 hx8_2 (by simpa using hx1_2)
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
      have hpb_eq : ({ uc := pb.uc, receivingEk := some d } : V1State.Chunked.HeaderReceived) = pb := by
        cases pb; simp at hek_opt; subst hek_opt; rfl
      rw [hpb_eq]
      exact e2b306r_outer_eq_exit hDom hsp_align hsome_full hrestOut_le hrestOut_suf
        hpc3 hrun3 hsp3 htr3 hx21_3 hx22_3 hcs3
  let cur0 := raw ++ restOut
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
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b306r_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
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
        e2b306r_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hcur0_le hcur0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      have hnil : evs_dv = [] := decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv
      subst hnil
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedHeaderReceivedPBCapAt_mono A.repAlloc x.msgPtr x.msg hcur0_le) (by sep_focus)
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
        (P' := e2b306r_outerPre A lim st s0 _ x default cur0 0 0)
        (by dsimp only [e2b306r_outerPre, sliceCursorAfter]; rw [hmsg]; sep_entail)
      have hcur0_split : cur0 =
          encodeOptMessage V1State.Unchunked.HeaderReceived.encodeRaw 1#32 pb.uc ++ cur1 := by
        dsimp only [cur0, raw, V1State.Chunked.HeaderReceived.encodeRaw, cur1]
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
        have hm0_eq : (default : V1State.Chunked.HeaderReceived) =
            { uc := pb.uc, receivingEk := none } := by
          rw [huc_opt]; rfl
        refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
          (P' := e2b306r_outerPre A lim st s0 _ x { uc := pb.uc, receivingEk := none } cur1
            (authOps + 2) 6946)
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
        dsimp only [e2b306r_outerPre]
        rw [hcur0_eq, hm0_eq]
        exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (b304PoolAt_mono A lim st (Nat.zero_le _) (Nat.zero_le _) _))))))
      · have hu : tlb_ValidUcHeaderReceivedPB u := hpb.1 u huc_opt
        let rest1 := tlb_lenPrefixed (V1State.Unchunked.HeaderReceived.encodeRaw u) cur1
        have hcur0_eq : cur0 = 0x0a#8 :: rest1 := by
          rw [hcur0_split, huc_opt]
          exact encodeOptMessage_tag1_some V1State.Unchunked.HeaderReceived.encodeRaw u cur1
        have hgt1 : restOut.length < cur0.length := by
          have hro_le_c1 : restOut.length ≤ cur1.length := by
            change restOut.length ≤ (encodeOptMessage PolynomialDecoder.encodeRaw 2#32 pb.receivingEk ++ restOut).length
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
        refine e2b306r_outer_step_key_varint hVarintCall hgt1 hsp_align hbs_lt hcur0_le hcur0_suf hd1
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
        apply sepWPpLscro_of_vm (mid := entry + 296#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvmA => ?_⟩
          have hdef_hr : (default : V1State.Chunked.HeaderReceived) = { uc := none, receivingEk := none } := rfl
          refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
            (P' := e2b306r_ucPre A lim st s0 _ x
              (optHeaderReceivedPBCapAt A.repAlloc x.msgPtr rest1.length none)
              rest1 0 0)
            ?_
            (e2b306r_uc_canonical_placed (outerLimit := restOut.length)
              hVarintCall hBytesCall hAuthTightCall (by omega : authOps + 2 ≤ maxOps)
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
          · dsimp only [e2b306r_outerPre, e2b306r_ucPre]
            rw [hdef_hr]
            dsimp only [chunkedHeaderReceivedPBCapAt]
            rw [b304PoolAt_eq_of_vmPreserved hvmA]
            exact Entails.of_eq (by sep_ac_rfl)
          · apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPpLscro.weaken_pre
              (P' := e2b306r_outerPre A lim st s0 sB x { uc := pb.uc, receivingEk := none }
                cur1 (authOps + 2) 6946)
              (by
                dsimp only [e2b306r_outerPre, e2b306r_ucPre, chunkedHeaderReceivedPBCapAt]
                rw [huc_opt]
                exact Entails.of_eq (by sep_ac_rfl))
            exact hPhase2 sB hcur1_le hcur1_suf
              hpcB hrunB hspB htrB hx19B hx20B hx21B hx22B hx23B hx24B hx25B hcsB

end ClPlaced

/-! ## 4. Exported Guarded-Tight Placed Contract (`e2b306r_`) -/

theorem e2b306r_chunkedHeaderReceivedMerge_placed_tight_ok_of_fallback [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps decOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + 2 + decOps ≤ maxOps)
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext)
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hFallback : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext))
      (lsmpl.base 306) (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim))) :
    tlb_ChunkedHeaderReceivedMergePlacedTightOkOf A lim maxOps ext := by
  unfold tlb_ChunkedHeaderReceivedMergePlacedTightOkOf
  apply subroutine_ok_outcome_intro
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : (libsignalSessionLib.blockProgram lsmpl 306 (Rust.withPanics ext)).CodeLoaded s0.mem :=
    hfr0.1 306 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  by_cases hDom : tlb_ChunkedHeaderReceivedDom x
  · have hDomOwn := e2b306r_own_of_blk_cro (e2b306r_dom_blk_ok A lim hOps
      (e2b306r_lift_cl_of_own hVarint)
      (e2b306r_lift_cro_of_own hBytes)
      (e2b306r_lift_cro_of_own hAuthTight)
      (e2b306r_lift_cro_of_own hDecTight))
    have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (e2b306r_domSpec A lim maxOps)).pre (x, st) s0 ∗ R :=
      Satisfies.of_entails hpre (sepConj_mono_left
        (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _))))
    obtain ⟨sf, hsteps, hout, _⟩ := hDomOwn.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_dom hsp hQL
    exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  · have hpre_fb : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (chunkedHeaderReceivedMergeSpec A lim)).pre (x, st) s0 ∗ R := by
      refine Satisfies.of_entails hpre (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedHeaderReceivedMergeSpec,
        chunkedHeaderReceivedMergeSpecOfEnv]
      refine sepConj_mono_left ?_
      exact Entails.pure_left fun ⟨h0, h1, h2, h3, hFit⟩ =>
        Entails.pure_right ⟨h0, h1, h2, h3, tlb_fitsEnv_fallback_of_not_dom hDom hFit⟩
          (Entails.refl _)
    obtain ⟨sf, hsteps, hout, _⟩ := hFallback.no_fault_before_outcome (x, st) R s0 hpc hrun hpre_fb hsp hQL
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, hp⟩ | ⟨hoom, hp⟩
    · refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
      refine Satisfies.of_entails hpost (sepConj_mono_left ?_)
      dsimp only [withLsCodeRoLoaded, chunkedHeaderReceivedMergeSpec,
        chunkedHeaderReceivedMergeSpecOfEnv]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      refine Entails.sepExists_elim fun evs => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro evs)
      exact Entails.pure_left fun hevs =>
        Entails.pure_right (Or.inr ⟨hDom, chunkedHeaderReceivedMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _)
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inl ⟨hpan, hp⟩)))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inl ⟨code, hex, hp⟩))))
    · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome (Or.inr (Or.inr (Or.inr ⟨hoom, hp⟩))))

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB306RPlacedBudget
