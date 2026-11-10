/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentClPlacedBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
import LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetSteps
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbLeaf
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbUnchunked
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Guarded-Tight Placed Budget Proof for `Chunked.HeaderSent::merge` (Block `302`)

Proves `tlb_ChunkedHeaderSentMergePlacedTightOkOf` on Block `302` within
`SpqrTightEvs maxOps 707760 2560` (`authOps + 2 + encOps + decOps ≤ maxOps`, default
`76 = 4 + 2 + 35 + 35`: inlined `Unchunked.EkSent` `22,530` B + `PolynomialEncoder` `342,615` B +
`PolynomialDecoder` `342,615` B) on canonical `tlb_ChunkedHeaderSentDom` inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB302PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecBuf vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_encodeVarint decodeVarint_length mergeBytes)
open CryptoVerification.LibsignalTripleRatchet
  (decodeErrorHookStack keys_ls_subroutine_ok_of_block_cro reserveCap
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk IsDropSuffix bytesMergeCapOk_zero decodeVarint_suffix
   sliceCursorAfter sliceCursorAfter_eq_split
   sliceCursorAt suffix_trans ule_len_of_ge)
open CryptoVerification.LibsignalSpqrV1
  (PolynomialDecoder PolynomialEncoder ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (AuthMergeGhost WppPost protoEncodeVarint_eq_codec setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderPinnedAt protoPolynomialEncoderPinnedAt vecVecU8PinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved OptPolyDecoderBound OptPolyEncoderBound
   PolyDecoderMergeGhost PolyEncoderMergeGhost SepWPpLscro blkPC_302 blkPl_302
   bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedHeaderSentMerge_fnOff chunkedHeaderSentPBCapAt chunkedHeaderSentPBCapAt_mono
   chunkedInlBelowStack chunkedInlSavedRegs10 codecWireTypeToProto
   polyDecoderToProto polyEncoderToProto proto_mergeMessage_suffix
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   vecU8At_eq_header_sep_buf vecU8Buf withLscroProp wt_beq_two_of_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved fitsEvents_append
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs spqrAllocTightCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOkOf
   tlb_ChunkedHeaderSentDom tlb_ChunkedHeaderSentGuardedEnvOf
   tlb_ChunkedHeaderSentMergePlacedTightOk tlb_ChunkedHeaderSentMergePlacedTightOkOf
   tlb_GuardedEnv tlb_PolyDecoderDom tlb_PolyDecoderGuardedEnvOf
   tlb_PolyDecoderMergePlacedTightOkOf tlb_PolyEncoderDom tlb_PolyEncoderGuardedEnvOf
   tlb_PolyEncoderMergePlacedTightOkOf tlb_ValidChunkedHeaderSentPB
   tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt
   tlb_domHeap_of_dom tlb_lenPrefixed
   tlb_polyDecoderMergeTightSpecOfEnv tlb_polyDecoderZeroCapAt tlb_polyDecoderZeroCapAt_of_ptr
   tlb_polyEncoderMergeTightSpecOfEnv tlb_polyEncoderZeroCapAt tlb_polyEncoderZeroCapAt_of_ptrs
   tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_of_ptr)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (AuthMergeEnv authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv chunkedHeaderSentMergePostEnv_imp_pre
   chunkedHeaderSentMergeSpec chunkedHeaderSentMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudget
  (chunked_header_sent_merge_cl_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   sepWPpLscro_of_ret_vm sepWPpLscro_of_vm sepWPpLscro_pure_elim vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyEncoderMergeEnv bytesMerge3RawBudgetSpec
   polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-! ## 1. Tight Event Envelope Lemmas (`bytesMergeEventsCore` at `valCap = 0#64`) -/

private theorem e2b302_reserveCap_zero_le_2560 {n : Nat} (hn : n ≤ 2400) :
    reserveCap 0 0 n ≤ 2560 := by
  unfold reserveCap
  omega

private theorem e2b302_spqrAllocTightCost_2560 :
    spqrAllocTightCost 2560 = 9789 := by decide

private theorem e2b302_spqrTightEvs_bytesMergeEventsCore_zero
    {bs rest' : List (BitVec 8)} {v : List (BitVec 8)}
    (hmb : mergeBytes .lengthDelimited bs = some (v, rest'))
    (hv : v.length ≤ 2400) :
    SpqrTightEvs 2 19578 2560 (bytesMergeEventsCore .lengthDelimited 0#64 bs) := by
  unfold bytesMergeEventsCore
  simp only [hmb]
  split
  · exact SpqrTightEvs.nil 2 19578 2560
  · rename_i hne
    have hvpos : ¬ v.length ≤ (0#64).toNat := by
      simp only [BitVec.toNat_ofNat]
      omega
    have hdrc : doReserveClearEvents (0#64).toNat v.length =
        rustAllocEvents (reserveCap 0 0 v.length) 1 := by
      unfold doReserveClearEvents
      simp only [BitVec.toNat_ofNat, Nat.zero_add] at hvpos ⊢
      simp [hvpos]
    rw [hdrc]
    have ha1 : SpqrTightEvs 1 9789 2560 (rustAllocEvents v.length 1) := by
      rw [← e2b302_spqrAllocTightCost_2560]
      exact SpqrTightEvs.rustAlloc (R := 2560) (req := v.length) (al := 1) (by omega) (by decide)
    have hrc : reserveCap 0 0 v.length ≤ 2560 := e2b302_reserveCap_zero_le_2560 hv
    have ha2 : SpqrTightEvs 1 9789 2560 (rustAllocEvents (reserveCap 0 0 v.length) 1) := by
      rw [← e2b302_spqrAllocTightCost_2560]
      exact SpqrTightEvs.rustAlloc (R := 2560) (req := reserveCap 0 0 v.length) (al := 1) hrc (by decide)
    have hd1 : SpqrTightEvs 0 0 0 (rustDeallocEvents v.length 1) :=
      SpqrTightEvs.rustDealloc v.length 1
    have h12 := (ha1.append ha2).append hd1
    simp only [List.append_assoc] at h12 ⊢
    exact h12.mono (by omega) (by omega) (by omega)

private theorem e2b302_tight_combine
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    {evsAuth evsDk evsEnc evsDec : List AllocEvent}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hE : SpqrTightEvs encOps encCum encReq evsEnc)
    (hD : SpqrTightEvs decOps decCum decReq evsDec) :
    SpqrTightEvs maxOps cumCap maxReq (evsAuth ++ evsDk ++ evsEnc ++ evsDec) := by
  have hA' : SpqrTightEvs authOps authCum maxReq evsAuth :=
    hA.mono (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hDk' : SpqrTightEvs 2 19578 maxReq evsDk :=
    hDk.mono (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hE' : SpqrTightEvs encOps encCum maxReq evsEnc :=
    hE.mono (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hD' : SpqrTightEvs decOps decCum maxReq evsDec :=
    hD.mono (Nat.le_refl _) (Nat.le_refl _) (by omega)
  have hAll := ((hA'.append hDk').append hE').append hD'
  simp only [List.append_assoc] at hAll ⊢
  exact hAll.mono hOps (by omega) (by omega)

/-! ## 2. Cross-Block Transfer & `bytesMerge3RawBudgetSpec` Bridge -/

private theorem e2b302_ls_subroutine_ok_cro_of_blockProgram_ext [LibsignalPlacement] {α : Type}
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

private theorem e2b302_bytesMerge3_poly_of_signed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program}
    {entry : BitVec 64}
    (h : subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim))) :
    subroutine_ok P entry
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim)).pre
          x s0 ∗ R := hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨h1, hq⟩ | ⟨h1, h2, hq⟩ | ⟨h1, hq⟩)
  · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
    dsimp only [withLsCodeRoLoaded,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec,
      bytesMerge3RawBudgetSpec]
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
    cases mergeBytes x.1.wt x.1.bs with
    | none => exact Entails.refl _
    | some vr =>
      rcases vr with ⟨v, rest⟩
      dsimp only
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
      refine Entails.sepExists_elim fun cap' => Entails.sepExists_right cap' ?_
      refine Entails.sepExists_elim fun ptr' => Entails.sepExists_right ptr' ?_
      exact Entails.pure_left fun hp => Entails.pure_right hp.1 (Entails.refl _)
  · exact Or.inr (Or.inl ⟨h1, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, hq⟩))

/-! ## 3. Guarded Envelope & Domain-Only Spec -/

def e2b302_ChunkedHeaderSentGuardedEnv (maxOps cumCap maxReq : Nat) :
    ChunkedHeaderSentMergeGhost → List AllocEvent → Prop :=
  tlb_GuardedEnv tlb_ChunkedHeaderSentDom
    (SpqrTightEvs maxOps cumCap maxReq) ChunkedHeaderSentMergeEnv

private noncomputable def e2b302_domOnlySpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps cumCap maxReq : Nat) :
    Spec (ChunkedHeaderSentMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜tlb_ChunkedHeaderSentDom x⌝ ∗
      (chunkedHeaderSentMergeSpecOfEnv A lim
        (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq)
        (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq)).pre (x, st) s
  post := (chunkedHeaderSentMergeSpecOfEnv A lim
    (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq)
    (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq)).post

section DomOnlyProof

open CryptoVerification.RustHeap (vecAt)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost bv32_zeroExtend_ofNat itag_beq_tag_false key_shr32_of_lt key_wt_some
   pointsToBytes_prefix_join sliceCursorAfter_join tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Auth
  (authenticatorPBCapAt memRegion_40_cells mergeBytes_length mergeBytes_suffix
   optAuthenticatorPBCapAt optAuthenticatorPBCapAt_mono)
open CryptoVerification.SpqrV1.Poly
  (protoPolynomialDecoderAt protoPolynomialEncoderAt)
open CryptoVerification.SpqrV1.ProtoRepr (optPolynomialDecoderPBAt optPolynomialEncoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (chunkedInlBelow_authMerge chunkedInlBelow_authMerge_entails
   chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_eq_polyMerge chunkedInlStack
   cmp_len_limit_of_eq cmp_len_limit_of_gt
   memRegion_polyDecoder_none_split_inl memRegion_polyEncoder_none_split_inl
   memRegion_unchunked3_none_split optEkSentPBCapAt optEkSentPBCapAt_mono
   optPolynomialDecoderPBAt_some_eq optPolynomialEncoderPBAt_some_eq
   pointsTo64_zero_split_32_inl
   stackAt_chunkedInl10_epilogue stackAt_chunkedInl_prologue unchunked3CapAt)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_ValidAuthPB tlb_ValidOptAuthPB tlb_ValidPolyDecoderPB tlb_ValidPolyEncoderPB
   tlb_ValidUcEkSentPB tlb_guardedEnv_tight_of_dom tlb_vecU8ZeroCapAt_entails_cap)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (AuthMergePostEnv authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (hsVecU8CapAt hsVecU8CapAt_mono unchunked3CapAt_eq vecU8At_entails_hsVecU8CapAt)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env PolyDecoderMergePostEnv PolyEncoderMergePostEnv
   polyDecoderMergeSpecOfEnv polyEncoderMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2SpecGen)

private theorem e2b302_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2b302_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2b302_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2b302_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2b302_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2b302_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2b302_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2b302_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2b302_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderSentMerge_fnOff
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2b302_sp_setMem_pre e2b302_pc_setMem_pre e2b302_status_setMem_pre e2b302_pstate_setMem_pre
  e2b302_trace_setMem_pre e2b302_readReg64_setMem_pre e2b302_readReg32_setMem_pre
  e2b302_readReg_setMem_pre e2b302_calleeSavedVRegs_setMem_pre

@[local simp, local arm64_norm]
private theorem e2b302_bv64_add24_add8 (a : BitVec 64) : a + 24#64 + 8#64 = a + 32#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add24_add16 (a : BitVec 64) : a + 24#64 + 16#64 = a + 40#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add24_add24 (a : BitVec 64) : a + 24#64 + 24#64 = a + 48#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add24_add32 (a : BitVec 64) : a + 24#64 + 32#64 = a + 56#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add24_add40 (a : BitVec 64) : a + 24#64 + 40#64 = a + 64#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add40_add8 (a : BitVec 64) : a + 40#64 + 8#64 = a + 48#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add8 (a : BitVec 64) : a + 80#64 + 8#64 = a + 88#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add16 (a : BitVec 64) : a + 80#64 + 16#64 = a + 96#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add24 (a : BitVec 64) : a + 80#64 + 24#64 = a + 104#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add32 (a : BitVec 64) : a + 80#64 + 32#64 = a + 112#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add40 (a : BitVec 64) : a + 80#64 + 40#64 = a + 120#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add80_add48 (a : BitVec 64) : a + 80#64 + 48#64 = a + 128#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add136_add8 (a : BitVec 64) : a + 136#64 + 8#64 = a + 144#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add136_add16 (a : BitVec 64) : a + 136#64 + 16#64 = a + 152#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add136_add24 (a : BitVec 64) : a + 136#64 + 24#64 = a + 160#64 := by
  bv_omega
@[local simp, local arm64_norm]
private theorem e2b302_bv64_add136_add32 (a : BitVec 64) : a + 136#64 + 32#64 = a + 168#64 := by
  bv_omega

private theorem e2b302_setWidth8_zext64_trunc32_ofNat64_wt (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

private theorem e2b302_stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

/-! ### Zero-Capacity Initialization Fold Lemmas (`cap = 0#64` for `dk`, `295`, `297`, `296`) -/

private theorem e2b302_pointsTo_zero_entails_vecU8ZeroCapAt (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b302_default_uc_entails_zeroDk (A : RustAlloc) (a : BitVec 64) (bsLen : Nat) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 32#64) 40 ∗
      ((a + 72#64) ↦₆₄ 0#64) ⊢
      tlb_vecU8ZeroCapAt A a [] ∗
        optAuthenticatorPBCapAt A (a + 0x18#64) bsLen none ∗
        ((a + 0x48#64) ↦₆₄ 0#64) := by
  dsimp only [optAuthenticatorPBCapAt]
  have h1 := e2b302_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h32 : a + 0x18#64 + 8#64 = a + 32#64 := by bv_omega
  rw [h32]
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗
    (((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (a + 32#64) 40) ∗
    ((a + 72#64) ↦₆₄ 0#64)
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

private theorem e2b302_default_auth_entails_zeroCap (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 0#64) ∗ ((a + 8#64) ↦₆₄ 1#64) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      ((a + 24#64) ↦₆₄ 0#64) ∗ ((a + 32#64) ↦₆₄ 1#64) ∗ ((a + 40#64) ↦₆₄ 0#64) ⊢
      tlb_authenticatorZeroCapAt A a default := by
  unfold tlb_authenticatorZeroCapAt
  change _ ⊢ tlb_vecU8ZeroCapAt A a [] ∗ tlb_vecU8ZeroCapAt A (a + 24#64) []
  have h1 := e2b302_pointsTo_zero_entails_vecU8ZeroCapAt A a 1#64 (by decide)
  have h2 := e2b302_pointsTo_zero_entails_vecU8ZeroCapAt A (a + 24#64) 1#64 (by decide)
  have h32 : a + 24#64 + 8#64 = a + 32#64 := by bv_lin
  have h40 : a + 24#64 + 16#64 = a + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 h2)

private theorem e2b302_pointsTo_zero_entails_vecVecU8ZeroPin (A : RustAlloc) (a ptr : BitVec 64)
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

private theorem e2b302_default_polyEncoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₆₄ 8#64) ∗ ((p + 40#64) ↦₆₄ 0#64) ∗
      ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4 ⊢
      tlb_polyEncoderZeroCapAt A p (polyEncoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyEncoderZeroCapAt_of_ptrs A 8#64 8#64 p (polyEncoderToProto default))
  unfold protoPolynomialEncoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    vecVecU8PinnedAt A ⟨0#64, 8#64⟩ (p + 24#64) [] ∗
    ((p + 48#64) ↦₃₂ 0#32) ∗ memRegion (p + 52#64) 4
  have h1 := e2b302_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h2 := e2b302_pointsTo_zero_entails_vecVecU8ZeroPin A (p + 24#64) 8#64 (by decide)
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_lin
  have h40 : p + 24#64 + 16#64 = p + 40#64 := by bv_lin
  rw [h32, h40] at h2
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))

private theorem e2b302_default_polyDecoder_entails_zeroCap (A : RustAlloc) (p : BitVec 64) :
    (p ↦₆₄ 0#64) ∗ ((p + 8#64) ↦₆₄ 8#64) ∗ ((p + 16#64) ↦₆₄ 0#64) ∗
      ((p + 24#64) ↦₆₄ 0#64) ∗ ((p + 32#64) ↦₈ 0#8) ∗ memRegion (p + 33#64) 7 ⊢
      tlb_polyDecoderZeroCapAt A p (polyDecoderToProto default) := by
  refine Entails.trans ?_ (tlb_polyDecoderZeroCapAt_of_ptr A 8#64 p (polyDecoderToProto default))
  unfold protoPolynomialDecoderPinnedAt
  change _ ⊢ vecVecU8PinnedAt A ⟨0#64, 8#64⟩ p [] ∗
    ((p + 24#64) ↦₃₂ 0#32) ∗
    ((p + 28#64) ↦₃₂ 0#32) ∗
    ((p + 32#64) ↦₈ 0#8) ∗
    memRegion (p + 33#64) 7
  have h1 := e2b302_pointsTo_zero_entails_vecVecU8ZeroPin A p 8#64 (by decide)
  have h28 : p + 24#64 + 4#64 = p + 28#64 := by bv_lin
  rw [pointsTo64_zero_split_32_inl (p + 24#64), h28]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl)) (sepConj_mono h1 (Entails.refl _))

/-! ### Pure Codec Round-Trip & Wire-Splitting Lemmas on `tlb_ChunkedHeaderSentDom` -/

private theorem e2b302_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> cases h
  rfl

private theorem e2b302_lenPrefixed_decodeVarint (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) = some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc, protoEncodeVarint_eq_codec]
  exact decodeVarint_encodeVarint (BitVec.ofNat 64 raw.length) (raw ++ rest)

private theorem e2b302_lenPrefixed_length_gt (raw rest : List (BitVec 8)) :
    raw.length + rest.length < (tlb_lenPrefixed raw rest).length := by
  simpa only [List.length_append] using
    decodeVarint_length (e2b302_lenPrefixed_decodeVarint raw rest)

private theorem e2b302_mergeMessage_ch_headerSent (pb : V1State.Chunked.HeaderSent)
    (rest : List (BitVec 8))
    (hraw : (V1State.Chunked.HeaderSent.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.Chunked.HeaderSent.mergeField .lengthDelimited default
      (tlb_lenPrefixed (V1State.Chunked.HeaderSent.encodeRaw pb) rest) 99).toOption =
      some (pb, rest) := by
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    V1State.Chunked.HeaderSent.mergeField 2 V1State.Chunked.HeaderSent.encodeRaw
    default pb 99 rest
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_ch_headerSent pb hraw) hraw (by decide)]
  rfl

private theorem e2b302_mergeMessage_auth (auth : ProtoAuthenticator)
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

private theorem e2b302_mergeMessage_polyEncoder (e : PolynomialEncoder)
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

private theorem e2b302_mergeMessage_polyDecoder (d : PolynomialDecoder)
    (after : List (BitVec 8))
    (hraw : (PolynomialDecoder.encodeRaw d).length < 2 ^ 64) :
    (mergeMessage PolynomialDecoder.mergeField
      (codecWireTypeToProto .lengthDelimited) default
      (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after) 98).toOption =
      some (d, after) := by
  change (mergeMessage PolynomialDecoder.mergeField .lengthDelimited
    default (tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after) 98).toOption =
    some (d, after)
  unfold tlb_lenPrefixed
  rw [List.append_assoc]
  rw [CryptoVerification.SpqrV1Sync.Codec.mergeMessage_encode
    PolynomialDecoder.mergeField 0 PolynomialDecoder.encodeRaw
    default d 98 after
    (CryptoVerification.SpqrV1Sync.Codec.loopsTo_polyDecoder d hraw) hraw (by decide)]
  rfl

private theorem e2b302_mergeBytes_lenPrefixed (v after : List (BitVec 8))
    (hv : v.length < 2 ^ 64) :
    mergeBytes .lengthDelimited (tlb_lenPrefixed v after) = some (v, after) := by
  unfold mergeBytes
  rw [e2b302_lenPrefixed_decodeVarint v after]
  have hlen : (BitVec.ofNat 64 v.length).toNat = v.length := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  have hge : ¬ (v ++ after).length < v.length := by
    simp only [List.length_append]
    omega
  simp [hlen, hge, List.take_append_of_le_length (Nat.le_refl _),
    List.drop_append_of_le_length (Nat.le_refl _)]

private theorem e2b302_encodeOptMessage_uc_tag1_some (u : V1State.Unchunked.EkSent)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.EkSent.encodeRaw 1#32 (some u) ++ after =
      0x0a#8 :: tlb_lenPrefixed (V1State.Unchunked.EkSent.encodeRaw u) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited =
      [0x0a#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b302_encodeOptMessage_polyEnc_tag2_some (e : PolynomialEncoder)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 (some e) ++ after =
      0x12#8 :: tlb_lenPrefixed (PolynomialEncoder.encodeRaw e) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited =
      [0x12#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b302_encodeOptMessage_polyDec_tag3_some (d : PolynomialDecoder)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialDecoder.encodeRaw 3#32 (some d) ++ after =
      0x1a#8 :: tlb_lenPrefixed (PolynomialDecoder.encodeRaw d) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
      [0x1a#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b302_encodeOptMessage_auth_tag2_some (auth : ProtoAuthenticator)
    (after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 (some auth) ++ after =
      0x12#8 :: tlb_lenPrefixed (ProtoAuthenticator.encodeRaw auth) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited =
      [0x12#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeMessage, hkey,
    tlb_lenPrefixed, List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b302_encodeBytesField_tag3_nonempty (b : BitVec 8) (bs after : List (BitVec 8)) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 (b :: bs) ++ after =
      0x1a#8 :: tlb_lenPrefixed (b :: bs) after := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 3#32 .lengthDelimited =
      [0x1a#8] := by decide
  simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
    CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesUncond, hkey,
    tlb_lenPrefixed, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
    List.cons_append, List.nil_append, List.append_assoc]

private theorem e2b302_decodeVarint_0x08 (r : List (BitVec 8)) :
    decodeVarint (0x08#8 :: r) = some (0x08#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x08#64 = [0x08#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x08#64 r

private theorem e2b302_decodeVarint_0x0a (r : List (BitVec 8)) :
    decodeVarint (0x0a#8 :: r) = some (0x0a#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x0a#64 = [0x0a#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x0a#64 r

private theorem e2b302_decodeVarint_0x12 (r : List (BitVec 8)) :
    decodeVarint (0x12#8 :: r) = some (0x12#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x12#64 = [0x12#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x12#64 r

private theorem e2b302_decodeVarint_0x1a (r : List (BitVec 8)) :
    decodeVarint (0x1a#8 :: r) = some (0x1a#64, r) := by
  have henc : CryptoVerification.LibsignalProtoCodec.encodeVarint 0x1a#64 = [0x1a#8] := by decide
  simpa only [henc, List.cons_append, List.nil_append] using decodeVarint_encodeVarint 0x1a#64 r

private theorem e2b302_decodeVarint_protoVarint (v : BitVec 64) (after : List (BitVec 8)) :
    decodeVarint (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint v ++ after) =
      some (v, after) := by
  rw [protoEncodeVarint_eq_codec]
  exact decodeVarint_encodeVarint v after

private theorem e2b302_headerSent_encodeRaw_split (pb : V1State.Chunked.HeaderSent)
    (after : List (BitVec 8)) :
    V1State.Chunked.HeaderSent.encodeRaw pb ++ after =
      CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.EkSent.encodeRaw 1#32 pb.uc ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 pb.sendingEk ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialDecoder.encodeRaw 3#32 pb.receivingCt1 ++ after)) := by
  unfold V1State.Chunked.HeaderSent.encodeRaw
  simp only [List.append_assoc]

private theorem e2b302_ekSent_encodeRaw_split (u : V1State.Unchunked.EkSent)
    (after : List (BitVec 8)) :
    V1State.Unchunked.EkSent.encodeRaw u ++ after =
      (if u.epoch == 0#64 then []
       else 0x08#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch) ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        ProtoAuthenticator.encodeRaw 2#32 u.auth ++
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 u.dk ++ after)) := by
  have hkey : CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .varint = [0x08#8] := by
    decide
  unfold V1State.Unchunked.EkSent.encodeRaw
  dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeUint64Field]
  split <;> simp only [hkey, List.cons_append, List.nil_append, List.append_assoc]

/-! ### Parametric `stepEvents` & `FitsEnv` Discharges -/

private theorem e2b302_stepEvents_nil {M : AllocCostModel} (st : M.σ) :
    M.stepEvents [] st = st := rfl

private theorem e2b302_stepEvents_append {M : AllocCostModel} (st : M.σ)
    (evs₁ evs₂ : List AllocEvent) :
    M.stepEvents evs₂ (M.stepEvents evs₁ st) = M.stepEvents (evs₁ ++ evs₂) st := by
  unfold AllocCostModel.stepEvents
  rw [List.foldl_append]

private theorem e2b302_fitsEnv_decodeVarint2_of_some {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} {p : BitVec 64 × List (BitVec 8)}
    (hd : decodeVarint bs = some p) :
    FitsEnv M lim st (DecodeVarint2Env bs) := by
  intro evs h
  rw [decodeVarint2Env_eq_nil_of_some hd h]
  trivial

private theorem e2b302_spqrTightEvs_bytesMerge3_zero
    {x_bm : BytesMergeGhost} {v rest' : List (BitVec 8)} {evs_bm : List AllocEvent}
    (hwt : x_bm.wt = .lengthDelimited)
    (hcap : x_bm.valCap = 0#64)
    (hmb : mergeBytes .lengthDelimited x_bm.bs = some (v, rest'))
    (hv : v.length ≤ 2400)
    (hevs : BytesMerge3Env x_bm evs_bm) :
    SpqrTightEvs 2 19578 2560 evs_bm := by
  unfold BytesMerge3Env
    LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget.BytesMerge3EnvCore at hevs
  rw [hwt, hcap] at hevs
  subst hevs
  exact e2b302_spqrTightEvs_bytesMergeEventsCore_zero hmb hv

private theorem e2b302_fitsEnv_auth_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    {evs : List AllocEvent} {x_auth : AuthMergeGhost}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hDom_auth : tlb_AuthDom x_auth)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evs st)
      (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv x_auth) := by
  intro evs_a h_a
  have htight_a : SpqrTightEvs authOps authCum authReq evs_a :=
    tlb_guardedEnv_tight_of_dom hDom_auth h_a
  have hA' : SpqrTightEvs authOps authCum authReq (evs ++ evs_a) :=
    (hevs.append htight_a).mono (by omega) (by omega) (by omega)
  have hcomb : SpqrTightEvs maxOps cumCap maxReq (evs ++ evs_a) := by
    simpa only [List.append_nil] using
      e2b302_tight_combine hOps hCum hReq hA' (.nil _ _ _) (.nil _ _ _) (.nil _ _ _)
  exact ((fitsEvents_append M lim evs evs_a st).mp (hFit (evs ++ evs_a) hcomb)).2

private theorem e2b302_fitsEnv_dk_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    {evsAuth : List AllocEvent} {x_bm : BytesMergeGhost} {v rest' : List (BitVec 8)}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hwt : x_bm.wt = .lengthDelimited)
    (hcap : x_bm.valCap = 0#64)
    (hmb : mergeBytes .lengthDelimited x_bm.bs = some (v, rest'))
    (hv : v.length ≤ 2400)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents evsAuth st) (BytesMerge3Env x_bm) := by
  intro evs_bm h_bm
  have hDk : SpqrTightEvs 2 19578 2560 evs_bm :=
    e2b302_spqrTightEvs_bytesMerge3_zero hwt hcap hmb hv h_bm
  have hcomb : SpqrTightEvs maxOps cumCap maxReq (evsAuth ++ evs_bm) := by
    simpa only [List.append_nil] using
      e2b302_tight_combine hOps hCum hReq hA hDk (.nil _ _ _) (.nil _ _ _)
  exact ((fitsEvents_append M lim evsAuth evs_bm st).mp (hFit (evsAuth ++ evs_bm) hcomb)).2

private theorem e2b302_fitsEnv_polyEnc_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    {evsAuth evsDk : List AllocEvent} {x_enc : PolyEncoderMergeGhost}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hDom_enc : tlb_PolyEncoderDom x_enc)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents (evsAuth ++ evsDk) st)
      (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq)
        PolyEncoderMergeEnv x_enc) := by
  intro evs_e h_e
  have hE : SpqrTightEvs encOps encCum encReq evs_e :=
    tlb_guardedEnv_tight_of_dom hDom_enc h_e
  have hcomb : SpqrTightEvs maxOps cumCap maxReq ((evsAuth ++ evsDk) ++ evs_e) := by
    simpa only [List.append_assoc, List.append_nil] using
      e2b302_tight_combine hOps hCum hReq hA hDk hE (.nil _ _ _)
  exact ((fitsEvents_append M lim (evsAuth ++ evsDk) evs_e st).mp
    (hFit ((evsAuth ++ evsDk) ++ evs_e) hcomb)).2

private theorem e2b302_fitsEnv_polyDec_tight {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    {evsAuth evsDk evsEnc : List AllocEvent} {x_dec : PolyDecoderMergeGhost}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hE : SpqrTightEvs encOps encCum encReq evsEnc)
    (hDom_dec : tlb_PolyDecoderDom x_dec)
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq)) :
    FitsEnv M lim (M.stepEvents (evsAuth ++ evsDk ++ evsEnc) st)
      (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq)
        PolyDecoderMergeEnv x_dec) := by
  intro evs_d h_d
  have hD : SpqrTightEvs decOps decCum decReq evs_d :=
    tlb_guardedEnv_tight_of_dom hDom_dec h_d
  have hcomb : SpqrTightEvs maxOps cumCap maxReq ((evsAuth ++ evsDk ++ evsEnc) ++ evs_d) := by
    simpa only [List.append_assoc] using
      e2b302_tight_combine hOps hCum hReq hA hDk hE hD
  exact ((fitsEvents_append M lim (evsAuth ++ evsDk ++ evsEnc) evs_d st).mp
    (hFit ((evsAuth ++ evsDk ++ evsEnc) ++ evs_d) hcomb)).2

/-! ### Domain-Only Loop Predicates & Outer Prologue / Exit / Key-Decode Steps -/

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

private noncomputable def e2b302_poolAt {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s : State) : SepProp :=
  A.pool lim (M.stepEvents evs st) s

private theorem e2b302_poolAt_of_vmPreserved {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {evs : List AllocEvent} {s s' : State}
    (hvm : VmPreserved s s') :
    e2b302_poolAt A lim st evs s' = e2b302_poolAt A lim st evs s :=
  A.pool_of_vmPreserved hvm

private theorem e2b302_pool_entails_poolAt_nil0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {evs_dv : List AllocEvent} (hnil : evs_dv = []) :
    A.pool lim (M.stepEvents evs_dv st) s ⊢ e2b302_poolAt A lim st [] s := by
  subst hnil; exact Entails.refl _

private theorem e2b302_pool_entails_poolAt_nil {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs evs_dv : List AllocEvent} (s : State)
    (hnil : evs_dv = []) :
    A.pool lim (M.stepEvents evs_dv (M.stepEvents evs st)) s ⊢ e2b302_poolAt A lim st evs s := by
  subst hnil; exact Entails.refl _

private theorem e2b302_pool_entails_poolAt_append {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs₁ evs₂ : List AllocEvent) (s : State) :
    A.pool lim (M.stepEvents evs₂ (M.stepEvents evs₁ st)) s ⊢
      e2b302_poolAt A lim st (evs₁ ++ evs₂) s := by
  rw [e2b302_stepEvents_append]
  exact Entails.refl _

private noncomputable def e2b302_domLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (m : V1State.Chunked.HeaderSent)
    (bs cur : List (BitVec 8)) : SepProp :=
  e2b302_poolAt A lim st evs s ∗
    chunkedHeaderSentPBCapAt A.repAlloc msgPtr cur.length m ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

private noncomputable def e2b302_domUcPreZeroDk {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder)
    (bs cur : List (BitVec 8)) : SepProp :=
  e2b302_poolAt A lim st evs s ∗
    tlb_vecU8ZeroCapAt A.repAlloc msgPtr [] ∗
    optAuthenticatorPBCapAt A.repAlloc (msgPtr + 0x18#64) cur.length auth ∗
    ((msgPtr + 0x48#64) ↦₆₄ epoch) ∗
    optPolynomialEncoderPBAt A.repAlloc (msgPtr + 80#64) sendingEk ∗
    optPolynomialDecoderPBAt A.repAlloc (msgPtr + 136#64) receivingCt1 ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

private noncomputable def e2b302_domUcLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr : BitVec 64) (uc : V1State.Unchunked.EkSent)
    (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder)
    (bs cur : List (BitVec 8)) : SepProp :=
  e2b302_poolAt A lim st evs s ∗
    unchunked3CapAt A.repAlloc msgPtr cur.length uc.epoch uc.auth uc.dk ∗
    optPolynomialEncoderPBAt A.repAlloc (msgPtr + 80#64) sendingEk ∗
    optPolynomialDecoderPBAt A.repAlloc (msgPtr + 136#64) receivingCt1 ∗
    stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
    chunkedInlSavedRegs10 s0.sp s0 ∗ (bufRef ↦₆₄ slot) ∗ sliceCursorAfter slot ptr bs cur

private theorem e2b302_zeroDk_entails_ucLoopPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (evs : List AllocEvent) (s0 s : State)
    (msgPtr bufRef slot ptr epoch : BitVec 64) (auth : Option ProtoAuthenticator)
    (sendingEk : Option PolynomialEncoder) (receivingCt1 : Option PolynomialDecoder)
    (bs cur : List (BitVec 8)) :
    e2b302_domUcPreZeroDk A lim st evs s0 s msgPtr bufRef slot ptr epoch auth
      sendingEk receivingCt1 bs cur ⊢
      e2b302_domUcLoopPre A lim st evs s0 s msgPtr bufRef slot ptr
        { epoch := epoch, auth := auth, dk := [] } sendingEk receivingCt1 bs cur := by
  dsimp only [e2b302_domUcPreZeroDk, e2b302_domUcLoopPre]
  rw [unchunked3CapAt_eq]
  have hdk : tlb_vecU8ZeroCapAt A.repAlloc msgPtr [] ⊢
      hsVecU8CapAt A.repAlloc msgPtr cur.length [] :=
    tlb_vecU8ZeroCapAt_entails_cap A.repAlloc msgPtr cur.length []
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdk)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem e2b302_ok_exit_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {maxOps cumCap maxReq : Nat} (st : M.σ)
    (x : ChunkedHeaderSentMergeGhost) (s0 s sf : State)
    (m : V1State.Chunked.HeaderSent) (cur : List (BitVec 8)) (evs : List AllocEvent)
    (hDom : tlb_ChunkedHeaderSentDom x)
    (hsome : (mergeMessage V1State.Chunked.HeaderSent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hvm : VmPreserved s sf)
    (htr : sf.trace = s0.trace) (hx0 : sf.readReg64 .x0 = 0#64)
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs) :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ e2b302_poolAt A lim st evs s))) ⊢
    (e2b302_domOnlySpec A lim maxOps cumCap maxReq).post (x, st) s0 sf := by
  dsimp only [e2b302_domOnlySpec, chunkedHeaderSentMergeSpecOfEnv, e2b302_poolAt]
  rw [hsome, htr, hx0]
  have hguard : e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq x evs :=
    Or.inl ⟨hDom, hevs⟩
  have hpool : A.pool lim (M.stepEvents evs st) s ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq x evs'⌝ ∗
          A.pool lim (M.stepEvents evs' st) sf := by
    refine Entails.trans ?_ (Entails.sepExists_right evs (Entails.pure_right hguard (Entails.refl _)))
    rw [A.pool_of_vmPreserved hvm]
    exact Entails.refl _
  refine Entails.pure_right rfl ?_
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl :
    stackAt s0.sp chunkedInlStack ∗
      (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          (sliceCursorAfter x.slot x.ptr x.bs cur ∗ A.pool lim (M.stepEvents evs st) s))) =
    (x.bufRef ↦₆₄ x.slot) ∗
      (A.pool lim (M.stepEvents evs st) s ∗
        (stackAt s0.sp chunkedInlStack ∗
          (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr cur.length m ∗
            sliceCursorAfter x.slot x.ptr x.bs cur))))) ?_
  exact sepConj_mono_right (sepConj_mono hpool
    (sepConj_mono_right (Entails.pure_right rfl (Entails.refl _))))

private theorem e2b302_dom_ok_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {cur : List (BitVec 8)} {evs : List AllocEvent}
    {outerLimit : Nat}
    (hDom : tlb_ChunkedHeaderSentDom x)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (heq_lim : cur.length = outerLimit)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hsome : (mergeMessage V1State.Chunked.HeaderSent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hevs : SpqrTightEvs maxOps cumCap maxReq evs)
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_ret_vm
  by_vm_steps
    (conv => arg 4; simp only [e2b302_domLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlSavedRegs10,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      arm64_norm, hsp])
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
      (e2b302_ok_exit_entails A lim st x s0 s _ m cur evs hDom hsome hvm
        (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm]) hevs)

private theorem e2b302_dom_prologue [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {len : BitVec 64} {rest0 : List (BitVec 8)}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (h_1 : (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat)
    (h_2 : s0.readReg64 .x1 = x.msgPtr) (h_3 : s0.readReg64 .x2 = x.bufRef)
    (hbs_lt : x.bs.length < 2 ^ 63) (hwt_ld : x.wt = .lengthDelimited)
    (hdv0 : decodeVarint x.bs = some (len, rest0))
    (hlt_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ (s' : State),
      s'.pc = entry + 168#64 → s'.status = .Running →
      s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st [] s0 s' x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R)) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s0
      (chunkedHeaderSentPBCapAt A.repAlloc x.msgPtr x.bs.length x.msg ∗
        (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
        A.pool lim st s0 ∗ stackAt s0.sp chunkedInlStack)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
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
            simp only [A.pool_of_vmPreserved hvm1, e2b302_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
      (by exact ⟨by simp only [arm64_norm, wp_norm, h_3], hbs_lt, e2b302_fitsEnv_decodeVarint2_of_some hdv0⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
    have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
    have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
    have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
    have hule := ule_len_of_ge hlt_len hrest0_lt
    have hsub := bv_len_sub_limit hlt_len
    apply sepWPpLscro_of_vm (mid := entry + 168#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b302_stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
        sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedHeaderSentPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
      apply SepWP.fold
        (e2b302_pool_entails_poolAt_nil0 A lim st sm
          (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_domLoopPre A lim st [] s0 _ x.msgPtr x.bufRef x.slot x.ptr
          x.msg x.bs rest0)
        (by dsimp only [e2b302_domLoopPre, sliceCursorAfter]; sep_entail)
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

private theorem e2b302_dom_outer_decode_key [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {cur rest : List (BitVec 8)}
    {key : BitVec 64} {iwt : WireType} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63)
    (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      s'.pc = entry + 220#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b302_domLoopPre, e2b302_poolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 188#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b302_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        e2b302_fitsEnv_decodeVarint2_of_some hd⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
    apply sepWPpLscro_of_vm (mid := entry + 220#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
        e2b302_stackAt_decodeVarint2_raw_eq, hd, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_dv
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedHeaderSentPBCapAt_mono A.repAlloc x.msgPtr m hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2b302_pool_entails_poolAt_nil A lim st sm
          (decodeVarint2Env_eq_nil_of_some hd hevs_dv))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (by dsimp only [e2b302_domLoopPre]; sep_entail)
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

private theorem e2b302_raw_lt_2pow64 {raw rest' rest bs : List (BitVec 8)}
    (hrest_eq : rest = tlb_lenPrefixed raw rest')
    (hrest_le : rest.length ≤ bs.length) (hbs_lt : bs.length < 2 ^ 63) :
    raw.length < 2 ^ 64 := by
  have hgt := e2b302_lenPrefixed_length_gt raw rest'
  rw [← hrest_eq] at hgt
  omega

private theorem e2b302_dom_tag1_uc_enter [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest rest0 : List (BitVec 8)}
    {len : BitVec 64} {outerLimit : Nat}
    (huc_none : m.uc = none)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hdv0 : decodeVarint rest = some (len, rest0))
    (hlt_len : ¬ rest0.length < len.toNat)
    (hcont : ∀ (s' : State),
      rest0.length ≤ x.bs.length → IsDropSuffix x.bs rest0 →
      s'.pc = entry + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 (rest0.length - len.toNat) →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domUcPreZeroDk A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          0#64 none m.sendingEk m.receivingCt1 x.bs rest0)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 1)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  apply sepWPpLscro_of_vm (mid := entry + 344#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domLoopPre, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domLoopPre]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 344#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs s
    apply sepWPpLscro_of_vm (mid := entry + 368#64)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domLoopPre, chunkedHeaderSentPBCapAt, huc_none,
        optEkSentPBCapAt, memRegion_unchunked3_none_split x.msgPtr])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro v72; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := e2b302_default_uc_entails_zeroDk A.repAlloc x.msgPtr rest.length
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_domUcPreZeroDk A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
          0#64 none m.sendingEk m.receivingCt1 x.bs rest)
        (by dsimp only [e2b302_domUcPreZeroDk]; sep_entail)
      generalize hs2_eq : State.setMem _ _ = s2
      have hpc2 : s2.pc = entry + 368#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm]
      have hrun2 : s2.status = .Running := by subst hs2_eq; simp only [arm64_norm, wp_norm, hrun1]
      have hsp2 : s2.sp = s0.sp - 128#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm, hsp1]
      have htr2 : s2.trace = s0.trace := by subst hs2_eq; simp only [arm64_norm, wp_norm, htr1]
      have hx0_2 : s2.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx0_1]
      have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.bufRef := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx19_1]
      have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx20_1]
      have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = x.slot := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx21_1]
      have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx22_1]
      have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx23_1]
      have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx24_1]
      have hx25_2 : s2.readReg64 (Reg.gpr 25#5) = 8#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx25_1]
      have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx27_1]
      have hx28_2 : s2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx28_1]
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hvregs_1]
      clear hs2_eq hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hvregs_1 s1
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
      by_vm_steps
        (conv => arg 4; rw [e2b302_domUcPreZeroDk, e2b302_poolAt,
          sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro (spec := decodeVarint2Spec A lim)
          (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
          (ret_pc := entry + 384#64) hVarintCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun2])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp2]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, e2b302_stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp2])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_2],
            hrest_lt,
            e2b302_fitsEnv_decodeVarint2_of_some hdv0⟩)
          (by dsimp only [restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp2,
          hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hvregs_2]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
        have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
        have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
        have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
        have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
        have hrest0_suf : IsDropSuffix x.bs rest0 :=
          suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
        have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        apply sepWPpLscro_of_vm (mid := entry + 464#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            e2b302_stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp2])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
          apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) none hrest0_le_rest) (by sep_focus)
          apply SepWP.fold
            (e2b302_pool_entails_poolAt_nil A lim st sm
              (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
          wp_steps
          apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← e2b302_poolAt_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b302_domUcPreZeroDk A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
              0#64 none m.sendingEk m.receivingCt1 x.bs rest0)
            (by dsimp only [e2b302_domUcPreZeroDk, sliceCursorAfter]; sep_entail)
          exact hcont _ hrest0_le hrest0_suf
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr2])
            (by simp only [arm64_norm, wp_norm, hx19_m])
            (by simp only [arm64_norm, wp_norm, hx20_m])
            (by simp only [arm64_norm, wp_norm, hx21_m])
            (by simp only [arm64_norm, wp_norm, hx22_m])
            (by simp only [arm64_norm, wp_norm, hx23_m])
            (by simp only [arm64_norm, wp_norm, hx24_m])
            (by simp only [arm64_norm, wp_norm, hx25_m])
            (by simp only [arm64_norm, wp_norm, hsm1, hsub])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b302_dom_uc_decode_key [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {cur rest : List (BitVec 8)} {key : BitVec 64} {iwt : WireType}
    {outerLimit innerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hd : decodeVarint cur = some (key, rest))
    (hk_ge : ¬ 2 ^ 32 ≤ key.toNat)
    (hwt : WireType.ofNat? (key.toNat % 8) = some iwt)
    (hitag0 : ¬ key.toNat / 8 < 1)
    (hcont : ∀ (s' : State),
      rest.length ≤ x.bs.length → IsDropSuffix x.bs rest →
      s'.pc = entry + 516#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domUcPreZeroDk A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          epoch auth sendingEk receivingCt1 x.bs rest)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domUcPreZeroDk A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr
        epoch auth sendingEk receivingCt1 x.bs cur)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [e2b302_domUcPreZeroDk, e2b302_poolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, M.stepEvents evs st))
      (ret_pc := entry + 484#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, e2b302_stackAt_decodeVarint2_raw_eq,
              arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx19],
        hcur_lt,
        e2b302_fitsEnv_decodeVarint2_of_some hd⟩)
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest :=
      suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    have hshr := key_shr32_of_lt hk_ge
    obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
    obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
    obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
    obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
    have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
    apply sepWPpLscro_of_vm (mid := entry + 516#64)
    by_vm_steps
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
        e2b302_stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
        sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) auth hrest_le_cur) (by sep_focus)
      apply SepWP.fold
        (e2b302_pool_entails_poolAt_nil A lim st sm
          (decodeVarint2Env_eq_nil_of_some hd hevs_v))
        (by sep_focus)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm2]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_domUcPreZeroDk A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
          epoch auth sendingEk receivingCt1 x.bs rest)
        (by dsimp only [e2b302_domUcPreZeroDk]; sep_entail)
      exact hcont _ hrest_le hrest_suf
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
        (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr])
        (by simp only [arm64_norm, wp_norm, hsm1, hand_wt])
        (by simp only [arm64_norm, wp_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
        (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
        (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
        (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
        (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
        ⟨by simp only [arm64_norm, wp_norm, hx27_m],
         by simp only [arm64_norm, wp_norm, hx28_m],
         by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b302_dom_uc_epoch_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {epoch v : BitVec 64} {auth : Option ProtoAuthenticator}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {rest rest' : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hdv : decodeVarint rest = some (v, rest'))
    (hcont : ∀ (s' : State),
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = entry + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domUcPreZeroDk A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          v auth sendingEk receivingCt1 x.bs rest')
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.varint.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 1)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domUcPreZeroDk A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr
        epoch auth sendingEk receivingCt1 x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply sepWPpLscro_of_vm (mid := entry + 604#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domUcPreZeroDk, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domUcPreZeroDk]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 604#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.varint.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx26_1 : s1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx26]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs s
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domUcPreZeroDk, e2b302_poolAt,
        sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (spec := decodeVarint2Spec A lim)
        (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
        (ret_pc := entry + 616#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, e2b302_stackAt_decodeVarint2_raw_eq,
                arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_1],
          hrest_lt,
          e2b302_fitsEnv_decodeVarint2_of_some hdv⟩)
        (by dsimp only [restPtr]; sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
      have hrest'_le_bs : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le hrest_le
      have hrest'_suf : IsDropSuffix x.bs rest' :=
        suffix_trans hrest_le hrest_suf hrest'_le (decodeVarint_suffix hdv)
      apply sepWPpLscro_of_vm (mid := entry + 464#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
          e2b302_stackAt_decodeVarint2_raw_eq,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (e2b302_pool_entails_poolAt_nil A lim st sm
            (decodeVarint2Env_eq_nil_of_some hdv hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← e2b302_poolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2b302_domUcPreZeroDk A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
            v auth sendingEk receivingCt1 x.bs rest')
          (by dsimp only [e2b302_domUcPreZeroDk]; sep_entail)
        exact hcont _ hrest'_le_bs hrest'_suf
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

private theorem e2b302_dom_uc_auth_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hAuthTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {epoch : BitVec 64} {authPb : ProtoAuthenticator}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {rest rest' : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hevs : SpqrTightEvs 0 0 0 evs)
    (hValid_auth : tlb_ValidAuthPB authPb)
    (hrest_eq : rest = tlb_lenPrefixed (ProtoAuthenticator.encodeRaw authPb) rest')
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evsAuth : List AllocEvent) (s' : State),
      SpqrTightEvs authOps authCum authReq evsAuth →
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = entry + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domUcPreZeroDk A lim st evsAuth s0 s' x.msgPtr x.bufRef x.slot x.ptr
          epoch (some authPb) sendingEk receivingCt1 x.bs rest')
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 2)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domUcPreZeroDk A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr
        epoch none sendingEk receivingCt1 x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  obtain ⟨hb1_1, hb1_2⟩ := itag_beq_tag_false (by decide : (2 : Nat) ≠ 1) (by decide : 2 < 2 ^ 32) (by decide)
  apply sepWPpLscro_of_vm (mid := entry + 560#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domUcPreZeroDk, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domUcPreZeroDk]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 560#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx26_1 : s1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx26]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs s
    apply sepWPpLscro_of_vm (mid := entry + 584#64)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domUcPreZeroDk, optAuthenticatorPBCapAt,
        memRegion_40_cells (x.msgPtr + 0x18#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro w1
      apply SepWP.exists_elim; intro w2
      apply SepWP.exists_elim; intro w3
      apply SepWP.exists_elim; intro w4
      apply SepWP.exists_elim; intro w5
      wp_steps
      have hdef := e2b302_default_auth_entails_zeroCap A.repAlloc (x.msgPtr + 0x18#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_poolAt A lim st evs _ ∗
          tlb_vecU8ZeroCapAt A.repAlloc x.msgPtr [] ∗
          tlb_authenticatorZeroCapAt A.repAlloc (x.msgPtr + 0x18#64) default ∗
          ((x.msgPtr + 0x48#64) ↦₆₄ epoch) ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 80#64) sendingEk ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 136#64) receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest)
        (by sep_entail)
      generalize hs2_eq : State.setMem _ _ = s2
      have hpc2 : s2.pc = entry + 584#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm]
      have hrun2 : s2.status = .Running := by subst hs2_eq; simp only [arm64_norm, wp_norm, hrun1]
      have hsp2 : s2.sp = s0.sp - 128#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm, hsp1]
      have htr2 : s2.trace = s0.trace := by subst hs2_eq; simp only [arm64_norm, wp_norm, htr1]
      have hx0_2 : s2.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx0_1]
      have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.bufRef := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx19_1]
      have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx20_1]
      have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = x.slot := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx21_1]
      have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx22_1]
      have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx23_1]
      have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx24_1]
      have hx25_2 : s2.readReg64 (Reg.gpr 25#5) = 8#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx25_1]
      have hx26_2 : s2.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx26_1]
      have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx27_1]
      have hx28_2 : s2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx28_1]
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hvregs_1]
      clear hs2_eq hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1 s1
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      let x_auth : AuthMergeGhost := ⟨.lengthDelimited, x.msgPtr + 0x18#64, default, x.bufRef, x.slot, restPtr, rest⟩
      have hDom_auth : tlb_AuthDom x_auth := ⟨rfl, rfl, authPb, rest', hValid_auth, hrest_eq⟩
      have hraw_auth : (ProtoAuthenticator.encodeRaw authPb).length < 2 ^ 64 :=
        e2b302_raw_lt_2pow64 hrest_eq hrest_le hbs_lt
      have hauth_res : (mergeMessage ProtoAuthenticator.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest 97).toOption = some (authPb, rest') := by
        rw [hrest_eq]
        exact e2b302_mergeMessage_auth authPb rest' hraw_auth
      apply sepWPpLscro_of_vm (mid := lsmpl.base 295)
      by_vm_steps
        (conv => arg 4; rw [e2b302_poolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedInlBelow_authMerge s0.sp])
        (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro
          (spec := tlb_authMergeTightSpecOfEnv A lim
            (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
            (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))
          (x := (x_auth, M.stepEvents evs st))
          (ret_pc := entry + 596#64) hAuthTightCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun2])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp2]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_authMergeTightSpecOfEnv, x_auth]
                rw [tlb_domHeap_of_dom hDom_auth]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, arm64_norm, wp_norm, hsp2])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_2, setWidth8_ofNat64_wt,
              e2b302_setWidth8_zext64_trunc32_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_2],
            by simp only [arm64_norm, wp_norm, hx19_2],
            hrest_lt,
            e2b302_fitsEnv_auth_tight hOps hCum hReq hevs hDom_auth hFit⟩)
          (by dsimp only [restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp2,
          hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hvregs_2]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
        obtain ⟨hrest'_le, hrest'_suf_r⟩ := proto_mergeMessage_suffix hauth_res
        have hrest'_le_bs : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le hrest_le
        have hrest'_suf : IsDropSuffix x.bs rest' :=
          suffix_trans hrest_le hrest_suf hrest'_le hrest'_suf_r
        apply sepWPpLscro_of_vm (mid := entry + 464#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_authMergeTightSpecOfEnv, authMergeSpecOfEnv, x_auth, hauth_res,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp2])
          apply SepWP.exists_elim; intro evs_auth
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_auth⟩, hsm0⟩
          have hA : SpqrTightEvs authOps authCum authReq (evs ++ evs_auth) :=
            (hevs.append (tlb_guardedEnv_tight_of_dom hDom_auth hevs_auth)).mono
              (by omega) (by omega) (by omega)
          apply SepWP.fold (chunkedInlBelow_authMerge_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
          apply SepWP.fold (e2b302_pool_entails_poolAt_append A lim st evs evs_auth sm) (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← e2b302_poolAt_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b302_domUcPreZeroDk A lim st (evs ++ evs_auth) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              epoch (some authPb) sendingEk receivingCt1 x.bs rest')
            (by dsimp only [e2b302_domUcPreZeroDk, optAuthenticatorPBCapAt]; sep_entail)
          exact hcont (evs ++ evs_auth) _ hA hrest'_le_bs hrest'_suf
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr2])
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

private theorem e2b302_dom_uc_dk_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hBytesCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evsAuth : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {epoch : BitVec 64} {auth : Option ProtoAuthenticator}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {dkBs rest rest' : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hdk_len : dkBs.length ≤ 2400)
    (hrest_eq : rest = tlb_lenPrefixed dkBs rest')
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evsDk : List AllocEvent) (s' : State),
      SpqrTightEvs 2 19578 2560 evsDk →
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = entry + 464#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domUcLoopPre A lim st (evsAuth ++ evsDk) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { epoch := epoch, auth := auth, dk := dkBs } sendingEk receivingCt1 x.bs rest')
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 516#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domUcPreZeroDk A lim st evsAuth s0 s x.msgPtr x.bufRef x.slot x.ptr
        epoch auth sendingEk receivingCt1 x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
  obtain ⟨hb1_1, hb1_2⟩ := itag_beq_tag_false (by decide : (3 : Nat) ≠ 1) (by decide : 3 < 2 ^ 32) (by decide)
  obtain ⟨hb2_1, hb2_2⟩ := itag_beq_tag_false (by decide : (3 : Nat) ≠ 2) (by decide : 3 < 2 ^ 32) (by decide)
  apply sepWPpLscro_of_vm (mid := entry + 440#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domUcPreZeroDk, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domUcPreZeroDk]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 440#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx26_1 : s1.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx26]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs s
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    have hmb : mergeBytes .lengthDelimited rest = some (dkBs, rest') := by
      rw [hrest_eq]
      exact e2b302_mergeBytes_lenPrefixed dkBs rest' (by omega)
    apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domUcPreZeroDk, tlb_vecU8ZeroCapAt, e2b302_poolAt,
        sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro ptr1
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      let x_bm : BytesMergeGhost := ⟨.lengthDelimited, x.msgPtr, 0#64, ptr1, [], x.bufRef, x.slot, restPtr, rest⟩
      have hFit_bm : FitsEnv M lim (M.stepEvents evsAuth st) (BytesMerge3Env x_bm) :=
        e2b302_fitsEnv_dk_tight hOps hCum hReq hA rfl rfl hmb hdk_len hFit
      refine call_budget_lscro (spec := bytesMerge3RawBudgetSpec A lim)
        (x := (x_bm, M.stepEvents evsAuth st))
        (ret_pc := entry + 452#64) hBytesCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [bytesMerge3RawBudgetSpec, x_bm]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt,
            e2b302_setWidth8_zext64_trunc32_ofNat64_wt],
          by simp only [arm64_norm, wp_norm, hx20_1],
          by simp only [arm64_norm, wp_norm, hx19_1],
          hrest_lt,
          bytesMergeCapOk_zero,
          hFit_bm⟩)
        (by dsimp only [restPtr]; sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
      have hrest'_le_bs : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le hrest_le
      have hrest'_suf : IsDropSuffix x.bs rest' :=
        suffix_trans hrest_le hrest_suf hrest'_le (mergeBytes_suffix hmb)
      apply sepWPpLscro_of_vm (mid := entry + 464#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        apply SepWP.exists_elim; intro cap1'
        apply SepWP.exists_elim; intro ptr1'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap1'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hDk : SpqrTightEvs 2 19578 2560 evs_bm :=
          e2b302_spqrTightEvs_bytesMerge3_zero rfl rfl hmb hdk_len hevs_bm
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8At_entails_hsVecU8CapAt A.repAlloc x.msgPtr cap1' ptr1' rest'.length dkBs hcap1') (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) auth hrest'_le) (by sep_focus)
        apply SepWP.fold (e2b302_pool_entails_poolAt_append A lim st evsAuth evs_bm sm) (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← e2b302_poolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := e2b302_domUcLoopPre A lim st (evsAuth ++ evs_bm) s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { epoch := epoch, auth := auth, dk := dkBs } sendingEk receivingCt1 x.bs rest')
          (by dsimp only [e2b302_domUcLoopPre]; rw [unchunked3CapAt_eq]; simp only [arm64_norm]; sep_entail)
        exact hcont evs_bm _ hDk hrest'_le_bs hrest'_suf
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

private theorem e2b302_dom_uc_exit [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {maxOps cumCap maxReq : Nat}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evs : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.EkSent}
    {sendingEk : Option PolynomialEncoder} {receivingCt1 : Option PolynomialDecoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (heq_lim : cur.length = innerLimit)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur)
    (hcont : ∀ (s' : State),
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st evs s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domUcLoopPre A lim st evs s0 s x.msgPtr x.bufRef x.slot x.ptr
        uc sendingEk receivingCt1 x.bs cur)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
  apply sepWPpLscro_of_vm (mid := entry + 168#64)
  by_vm_steps
    (conv => arg 4; rw [e2b302_domUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt])
    wp_steps
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm => ?_⟩
    rw [← e2b302_poolAt_of_vmPreserved hvm]
    apply SepWPpLscro.weaken_pre
      (P' := e2b302_domLoopPre A lim st evs s0 _ x.msgPtr x.bufRef x.slot x.ptr
        { uc := some uc, sendingEk := sendingEk, receivingCt1 := receivingCt1 } x.bs cur)
      (by dsimp only [e2b302_domLoopPre, chunkedHeaderSentPBCapAt,
            optEkSentPBCapAt, sliceCursorAfter]; sep_entail)
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

private theorem e2b302_dom_tag2_ek_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hPolyEncTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evsAuth evsDk : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {encPb : PolynomialEncoder}
    {rest rest' : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hek_none : m.sendingEk = none)
    (hValid_enc : tlb_ValidPolyEncoderPB encPb)
    (hrest_eq : rest = tlb_lenPrefixed (PolynomialEncoder.encodeRaw encPb) rest')
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evsEnc : List AllocEvent) (s' : State),
      SpqrTightEvs encOps encCum encReq evsEnc →
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingEk := some encPb } x.bs rest')
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 2)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st (evsAuth ++ evsDk) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt56 : rest.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_le hbs_lt56
  obtain ⟨hb1_1, hb1_2⟩ := itag_beq_tag_false (by decide : (2 : Nat) ≠ 1) (by decide : 2 < 2 ^ 32) (by decide)
  apply sepWPpLscro_of_vm (mid := entry + 292#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domLoopPre, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domLoopPre]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 292#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs s
    apply sepWPpLscro_of_vm (mid := entry + 320#64)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domLoopPre, chunkedHeaderSentPBCapAt, hek_none,
        optPolynomialEncoderPBAt, memRegion_polyEncoder_none_split_inl (x.msgPtr + 80#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40
      apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := e2b302_default_polyEncoder_entails_zeroCap A.repAlloc (x.msgPtr + 80#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_poolAt A lim st (evsAuth ++ evsDk) _ ∗
          optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          tlb_polyEncoderZeroCapAt A.repAlloc (x.msgPtr + 80#64) (polyEncoderToProto default) ∗
          optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 136#64) m.receivingCt1 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest)
        (by sep_entail)
      generalize hs2_eq : State.setMem _ _ = s2
      have hpc2 : s2.pc = entry + 320#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm]
      have hrun2 : s2.status = .Running := by subst hs2_eq; simp only [arm64_norm, wp_norm, hrun1]
      have hsp2 : s2.sp = s0.sp - 128#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm, hsp1]
      have htr2 : s2.trace = s0.trace := by subst hs2_eq; simp only [arm64_norm, wp_norm, htr1]
      have hx0_2 : s2.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx0_1]
      have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.bufRef := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx19_1]
      have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx20_1]
      have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = x.slot := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx21_1]
      have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx22_1]
      have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx23_1]
      have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx24_1]
      have hx25_2 : s2.readReg64 (Reg.gpr 25#5) = 8#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx25_1]
      have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx27_1]
      have hx28_2 : s2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx28_1]
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hvregs_1]
      clear hs2_eq hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hvregs_1 s1
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      let x_poly : PolyEncoderMergeGhost := ⟨.lengthDelimited, x.msgPtr + 80#64, default, x.bufRef, x.slot, restPtr, rest⟩
      have hDom_enc : tlb_PolyEncoderDom x_poly := ⟨rfl, rfl, encPb, rest', hValid_enc, hrest_eq⟩
      have hraw_enc : (PolynomialEncoder.encodeRaw encPb).length < 2 ^ 64 :=
        e2b302_raw_lt_2pow64 hrest_eq hrest_le hbs_lt
      have hpoly_res : (mergeMessage PolynomialEncoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (encPb, rest') := by
        rw [hrest_eq]
        exact e2b302_mergeMessage_polyEncoder encPb rest' hraw_enc
      have hpts0 : (default : PolynomialEncoder).pts.length + rest.length < 2 ^ 56 := by
        change 0 + rest.length < 2 ^ 56; omega
      have hpolys0 : (default : PolynomialEncoder).polys.length + rest.length < 2 ^ 56 := by
        change 0 + rest.length < 2 ^ 56; omega
      apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
      by_vm_steps
        (conv => arg 4; rw [e2b302_poolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedInlBelow_eq_polyMerge s0.sp])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro
          (spec := tlb_polyEncoderMergeTightSpecOfEnv A lim
            (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
            (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))
          (x := (x_poly, M.stepEvents (evsAuth ++ evsDk) st))
          (ret_pc := entry + 332#64) hPolyEncTightCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun2])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp2]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_polyEncoderMergeTightSpecOfEnv, x_poly]
                rw [tlb_domHeap_of_dom hDom_enc]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, arm64_norm, wp_norm, hsp2])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_2, setWidth8_ofNat64_wt,
              e2b302_setWidth8_zext64_trunc32_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_2],
            by simp only [arm64_norm, wp_norm, hx19_2],
            hpts0,
            hpolys0,
            e2b302_fitsEnv_polyEnc_tight hOps hCum hReq hA hDk hDom_enc hFit⟩)
          (by dsimp only [restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp2,
          hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hvregs_2]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
        obtain ⟨hrest'_le, hrest'_suf_r⟩ := proto_mergeMessage_suffix hpoly_res
        have hrest'_le_bs : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le hrest_le
        have hrest'_suf : IsDropSuffix x.bs rest' :=
          suffix_trans hrest_le hrest_suf hrest'_le hrest'_suf_r
        apply sepWPpLscro_of_vm (mid := entry + 168#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_polyEncoderMergeTightSpecOfEnv, polyEncoderMergeSpecOfEnv,
            PolyEncoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_p
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_p
          wp_focus_pure; intro hsm0
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp2])
          have hE : SpqrTightEvs encOps encCum encReq evs_p :=
            tlb_guardedEnv_tight_of_dom hDom_enc hevs_p
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
          apply SepWP.fold (optEkSentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
          apply SepWP.fold (e2b302_pool_entails_poolAt_append A lim st (evsAuth ++ evsDk) evs_p sm) (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← e2b302_poolAt_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evs_p) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with sendingEk := some encPb } x.bs rest')
            (by dsimp only [e2b302_domLoopPre, chunkedHeaderSentPBCapAt];
                rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
          exact hcont evs_p _ hE hrest'_le_bs hrest'_suf
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr2])
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

private theorem e2b302_dom_tag3_ct1_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hPolyDecTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evsAuth evsDk evsEnc : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {decPb : PolynomialDecoder}
    {rest rest' : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hE : SpqrTightEvs encOps encCum encReq evsEnc)
    (hct1_none : m.receivingCt1 = none)
    (hValid_dec : tlb_ValidPolyDecoderPB decPb)
    (hrest_eq : rest = tlb_lenPrefixed (PolynomialDecoder.encodeRaw decPb) rest')
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hcont : ∀ (evsDec : List AllocEvent) (s' : State),
      SpqrTightEvs decOps decCum decReq evsDec →
      rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc ++ evsDec) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with receivingCt1 := some decPb } x.bs rest')
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc) s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  have hrest_lt56 : rest.length < 2 ^ 56 := Nat.lt_of_le_of_lt hrest_le hbs_lt56
  obtain ⟨hb1_1, hb1_2⟩ := itag_beq_tag_false (by decide : (3 : Nat) ≠ 1) (by decide : 3 < 2 ^ 32) (by decide)
  obtain ⟨hb2_1, hb2_2⟩ := itag_beq_tag_false (by decide : (3 : Nat) ≠ 2) (by decide : 3 < 2 ^ 32) (by decide)
  apply sepWPpLscro_of_vm (mid := entry + 244#64)
  by_vm_steps
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm0 => ?_⟩
    rw [e2b302_domLoopPre, ← e2b302_poolAt_of_vmPreserved hvm0, ← e2b302_domLoopPre]
    generalize hs1_eq : State.setPC _ _ = s1
    have hpc1 : s1.pc = entry + 244#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm]
    have hrun1 : s1.status = .Running := by subst hs1_eq; simp only [arm64_norm, wp_norm, hrun]
    have hsp1 : s1.sp = s0.sp - 128#64 := by subst hs1_eq; simp only [arm64_norm, wp_norm, hsp]
    have htr1 : s1.trace = s0.trace := by subst hs1_eq; simp only [arm64_norm, wp_norm, htr]
    have hx0_1 : s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx0]
    have hx19_1 : s1.readReg64 (Reg.gpr 19#5) = x.bufRef := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx19]
    have hx20_1 : s1.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx20]
    have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = x.slot := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx21]
    have hx22_1 : s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx22]
    have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = 1#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx23]
    have hx24_1 : s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx24]
    have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = 8#64 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx25]
    have hx27_1 : s1.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx27]
    have hx28_1 : s1.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hx28]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
      subst hs1_eq; simp only [arm64_norm, wp_norm, hvregs]
    clear hs1_eq hvm0 hpc hrun hsp htr hx0 hx1 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs s
    apply sepWPpLscro_of_vm (mid := entry + 268#64)
    by_vm_steps
      (conv => arg 4; rw [e2b302_domLoopPre, chunkedHeaderSentPBCapAt, hct1_none,
        optPolynomialDecoderPBAt, memRegion_polyDecoder_none_split_inl (x.msgPtr + 136#64)])
      (conv => arg 4; simp only [noneCap, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
      apply SepWP.exists_elim; intro b32; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v16; apply SepWP.exists_elim; intro v8
      wp_steps
      have hdef := e2b302_default_polyDecoder_entails_zeroCap A.repAlloc (x.msgPtr + 136#64)
      simp only [arm64_norm] at hdef
      apply SepWP.fold hdef (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← e2b302_poolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := e2b302_poolAt A lim st (evsAuth ++ evsDk ++ evsEnc) _ ∗
          optEkSentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
          optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 80#64) m.sendingEk ∗
          tlb_polyDecoderZeroCapAt A.repAlloc (x.msgPtr + 136#64) (polyDecoderToProto default) ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          chunkedInlSavedRegs10 s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest)
        (by sep_entail)
      generalize hs2_eq : State.setMem _ _ = s2
      have hpc2 : s2.pc = entry + 268#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm]
      have hrun2 : s2.status = .Running := by subst hs2_eq; simp only [arm64_norm, wp_norm, hrun1]
      have hsp2 : s2.sp = s0.sp - 128#64 := by subst hs2_eq; simp only [arm64_norm, wp_norm, hsp1]
      have htr2 : s2.trace = s0.trace := by subst hs2_eq; simp only [arm64_norm, wp_norm, htr1]
      have hx0_2 : s2.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 WireType.lengthDelimited.toNat := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx0_1]
      have hx19_2 : s2.readReg64 (Reg.gpr 19#5) = x.bufRef := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx19_1]
      have hx20_2 : s2.readReg64 (Reg.gpr 20#5) = x.msgPtr := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx20_1]
      have hx21_2 : s2.readReg64 (Reg.gpr 21#5) = x.slot := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx21_1]
      have hx22_2 : s2.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx22_1]
      have hx23_2 : s2.readReg64 (Reg.gpr 23#5) = 1#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx23_1]
      have hx24_2 : s2.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx24_1]
      have hx25_2 : s2.readReg64 (Reg.gpr 25#5) = 8#64 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx25_1]
      have hx27_2 : s2.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx27_1]
      have hx28_2 : s2.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hx28_1]
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
        subst hs2_eq; simp only [arm64_norm, wp_norm, hvregs_1]
      clear hs2_eq hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx28_1 hvregs_1 s1
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      let x_poly : PolyDecoderMergeGhost := ⟨.lengthDelimited, x.msgPtr + 136#64, default, x.bufRef, x.slot, restPtr, rest⟩
      have hDom_dec : tlb_PolyDecoderDom x_poly := ⟨rfl, rfl, decPb, rest', hValid_dec, hrest_eq⟩
      have hraw_dec : (PolynomialDecoder.encodeRaw decPb).length < 2 ^ 64 :=
        e2b302_raw_lt_2pow64 hrest_eq hrest_le hbs_lt
      have hpoly_res : (mergeMessage PolynomialDecoder.mergeField
          (codecWireTypeToProto .lengthDelimited) default rest 98).toOption = some (decPb, rest') := by
        rw [hrest_eq]
        exact e2b302_mergeMessage_polyDecoder decPb rest' hraw_dec
      have hpts0 : (default : PolynomialDecoder).pts.length + rest.length < 2 ^ 56 := by
        change 0 + rest.length < 2 ^ 56; omega
      apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
      by_vm_steps
        (conv => arg 4; rw [e2b302_poolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
          chunkedInlBelow_eq_polyMerge s0.sp])
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        refine call_budget_lscro
          (spec := tlb_polyDecoderMergeTightSpecOfEnv A lim
            (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)
            (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv))
          (x := (x_poly, M.stepEvents (evsAuth ++ evsDk ++ evsEnc) st))
          (ret_pc := entry + 280#64) hPolyDecTightCall
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun2])
          (by simp only [State.spAligned, arm64_norm, wp_norm, hsp2]; exact hsp_align)
          (by simp only [arm64_norm, wp_norm])
          (by conv =>
                lhs
                dsimp only [tlb_polyDecoderMergeTightSpecOfEnv, x_poly]
                rw [tlb_domHeap_of_dom hDom_dec]
                arg 2
                simp only [A.pool_of_vmPreserved hvm2, arm64_norm, wp_norm, hsp2])
          (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_2, setWidth8_ofNat64_wt,
              e2b302_setWidth8_zext64_trunc32_ofNat64_wt],
            by simp only [arm64_norm, wp_norm, hx20_2],
            by simp only [arm64_norm, wp_norm, hx19_2],
            hpts0,
            e2b302_fitsEnv_polyDec_tight hOps hCum hReq hA hDk hE hDom_dec hFit⟩)
          (by dsimp only [restPtr]; sep_focus) ?_
        intro sm hpcm hrunm hspm hcsm
        simp only [CalleeSavedPreserved] at hcsm
        obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
        simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp2,
          hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx27_2, hx28_2, hvregs_2]
          at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
        obtain ⟨hrest'_le, hrest'_suf_r⟩ := proto_mergeMessage_suffix hpoly_res
        have hrest'_le_bs : rest'.length ≤ x.bs.length := Nat.le_trans hrest'_le hrest_le
        have hrest'_suf : IsDropSuffix x.bs rest' :=
          suffix_trans hrest_le hrest_suf hrest'_le hrest'_suf_r
        apply sepWPpLscro_of_vm (mid := entry + 168#64)
        by_vm_steps
          (conv => arg 4; simp only [tlb_polyDecoderMergeTightSpecOfEnv, polyDecoderMergeSpecOfEnv,
            PolyDecoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_p
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_p
          wp_focus_pure; intro hsm0
          (conv => arg 4; simp only [arm64_norm, wp_norm, hsp2])
          have hD : SpqrTightEvs decOps decCum decReq evs_p :=
            tlb_guardedEnv_tight_of_dom hDom_dec hevs_p
          apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
          apply SepWP.fold (optEkSentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
          apply SepWP.fold (e2b302_pool_entails_poolAt_append A lim st (evsAuth ++ evsDk ++ evsEnc) evs_p sm) (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
          rw [← e2b302_poolAt_of_vmPreserved hvm3]
          apply SepWPpLscro.weaken_pre
            (P' := e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc ++ evs_p) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with receivingCt1 := some decPb } x.bs rest')
            (by dsimp only [e2b302_domLoopPre, chunkedHeaderSentPBCapAt];
                rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
          exact hcont evs_p _ hD hrest'_le_bs hrest'_suf
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr2])
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

private theorem e2b302_dom_stage1_uc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.EkSent} {after1 : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hValid_uc : ∀ u, ucOpt = some u → tlb_ValidUcEkSentPB u)
    (hafter_ge : outerLimit ≤ after1.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      V1State.Unchunked.EkSent.encodeRaw 1#32 ucOpt ++ after1).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        V1State.Unchunked.EkSent.encodeRaw 1#32 ucOpt ++ after1))
    (hcont : ∀ (evsAuth evsDk : List AllocEvent) (s' : State),
      SpqrTightEvs authOps authCum authReq evsAuth →
      SpqrTightEvs 2 19578 2560 evsDk →
      after1.length ≤ x.bs.length → IsDropSuffix x.bs after1 →
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st (evsAuth ++ evsDk) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, sendingEk := none, receivingCt1 := none } x.bs after1)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st [] s0 s x.msgPtr x.bufRef x.slot x.ptr
        { uc := none, sendingEk := none, receivingCt1 := none } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          V1State.Unchunked.EkSent.encodeRaw 1#32 ucOpt ++ after1))
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  cases ucOpt with
  | none =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
      at hcur_le hcur_suf ⊢
    exact hcont [] [] s (.nil _ _ _) (.nil _ _ _) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | some u =>
    obtain ⟨hValid_auth_opt, hdk_len⟩ := hValid_uc u rfl
    rw [e2b302_encodeOptMessage_uc_tag1_some u after1] at hcur_le hcur_suf ⊢
    let raw_u := V1State.Unchunked.EkSent.encodeRaw u
    let rest_u := tlb_lenPrefixed raw_u after1
    change (0x0a#8 :: rest_u).length ≤ x.bs.length at hcur_le
    change IsDropSuffix x.bs (0x0a#8 :: rest_u) at hcur_suf
    have hgt_lp : raw_u.length + after1.length < rest_u.length :=
      e2b302_lenPrefixed_length_gt raw_u after1
    have hcur_gt : ¬ (0x0a#8 :: rest_u).length ≤ outerLimit := by
      simp only [List.length_cons]; omega
    have hcur_lt : (0x0a#8 :: rest_u).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hd_0a : decodeVarint (0x0a#8 :: rest_u) = some (0x0a#64, rest_u) :=
      e2b302_decodeVarint_0x0a rest_u
    have hrest_u_le : rest_u.length ≤ x.bs.length := by
      simp only [List.length_cons] at hcur_le; omega
    have hrest_u_suf : IsDropSuffix x.bs rest_u :=
      suffix_trans hcur_le hcur_suf (by simp only [List.length_cons]; omega)
        (decodeVarint_suffix hd_0a)
    refine e2b302_dom_outer_decode_key hVarintCall hcur_gt hsp_align hcur_le hcur_lt hcur_suf
      hd_0a (by decide) (by decide : WireType.ofNat? ((0x0a#64).toNat % 8) = some .lengthDelimited)
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    have hx1_1' : s1.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 1 := by
      have hk : BitVec.ofNat 64 ((0x0a#64).toNat / 8) = BitVec.ofNat 64 1 := by decide
      rwa [hk] at hx1_1
    have hraw_u_lt64 : raw_u.length < 2 ^ 64 := by omega
    have hlen_u : (BitVec.ofNat 64 raw_u.length).toNat = raw_u.length := by
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_u_lt64]
    have hdv_u : decodeVarint rest_u = some (BitVec.ofNat 64 raw_u.length, raw_u ++ after1) :=
      e2b302_lenPrefixed_decodeVarint raw_u after1
    have hlt_u : ¬ (raw_u ++ after1).length < (BitVec.ofNat 64 raw_u.length).toNat := by
      rw [hlen_u, List.length_append]; omega
    have hinner_lim : (raw_u ++ after1).length - (BitVec.ofNat 64 raw_u.length).toNat = after1.length := by
      rw [hlen_u, List.length_append]; omega
    refine e2b302_dom_tag1_uc_enter hVarintCall rfl hsp_align hbs_lt hrest_u_le hrest_u_suf
      hdv_u hlt_u ?_ hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    intro s2 hbody_le hbody_suf hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    rw [hinner_lim] at hx26_2
    let after_auth := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 3#32 u.dk ++ after1
    let after_ep := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      ProtoAuthenticator.encodeRaw 2#32 u.auth ++ after_auth
    have hsplit_u : raw_u ++ after1 =
        (if u.epoch == 0#64 then []
         else 0x08#8 :: CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch) ++ after_ep :=
      e2b302_ekSent_encodeRaw_split u after1
    rw [hsplit_u] at hbody_le hbody_suf ⊢
    suffices h_after_ep : ∀ (s3 : State),
        after_ep.length ≤ x.bs.length → IsDropSuffix x.bs after_ep →
        s3.pc = entry + 464#64 →
        s3.status = .Running → s3.sp = s0.sp - 128#64 → s3.trace = s0.trace →
        s3.readReg64 (Reg.gpr 19#5) = x.bufRef → s3.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s3.readReg64 (Reg.gpr 21#5) = x.slot → s3.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s3.readReg64 (Reg.gpr 23#5) = 1#64 → s3.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
        s3.readReg64 (Reg.gpr 25#5) = 8#64 → s3.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 after1.length →
        ChunkedInl10CalleeSaved s0 s3 →
        SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s3
          (e2b302_domUcPreZeroDk A lim st [] s0 s3 x.msgPtr x.bufRef x.slot x.ptr
            u.epoch none none none x.bs after_ep)
          (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
          (WppPanicFalse R) by
      by_cases hep0 : (u.epoch == 0#64) = true
      · have hep_eq : u.epoch = 0#64 := beq_iff_eq.mp hep0
        simp only [hep0, ↓reduceIte, List.nil_append] at hbody_le hbody_suf ⊢
        rw [← hep_eq]
        exact h_after_ep s2 hbody_le hbody_suf hpc2 hrun2 hsp2 htr2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
      · simp only [hep0, Bool.false_eq_true, ↓reduceIte, List.cons_append] at hbody_le hbody_suf ⊢
        have hep_gt : ¬ (0x08#8 :: (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch ++ after_ep)).length ≤ after1.length := by
          dsimp only [after_ep, after_auth]
          simp only [List.length_cons, List.length_append]
          omega
        have hd_08 := e2b302_decodeVarint_0x08
          (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint u.epoch ++ after_ep)
        refine e2b302_dom_uc_decode_key hVarintCall hep_gt hsp_align hbs_lt hbody_le hbody_suf
          hd_08 (by decide) (by decide : WireType.ofNat? ((0x08#64).toNat % 8) = some .varint)
          (by decide) ?_ hpc2 hrun2 hsp2 htr2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
        intro s2' hep_rest_le hep_rest_suf hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2'
          hx19_2' hx20_2' hx21_2' hx22_2' hx23_2' hx24_2' hx25_2' hx26_2' hcs2'
        have hx1_2'' : s2'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 1 := by
          have hk : BitVec.ofNat 64 ((0x08#64).toNat / 8) = BitVec.ofNat 64 1 := by decide
          rwa [hk] at hx1_2'
        refine e2b302_dom_uc_epoch_step hVarintCall hsp_align hbs_lt hep_rest_le hep_rest_suf
          (e2b302_decodeVarint_protoVarint u.epoch after_ep) h_after_ep
          hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2''
          hx19_2' hx20_2' hx21_2' hx22_2' hx23_2' hx24_2' hx25_2' hx26_2' hcs2'
    intro s3 hafter_ep_le hafter_ep_suf hpc3 hrun3 hsp3 htr3
      hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hcs3
    suffices h_after_auth : ∀ (evsAuth : List AllocEvent) (s4 : State),
        SpqrTightEvs authOps authCum authReq evsAuth →
        after_auth.length ≤ x.bs.length → IsDropSuffix x.bs after_auth →
        s4.pc = entry + 464#64 →
        s4.status = .Running → s4.sp = s0.sp - 128#64 → s4.trace = s0.trace →
        s4.readReg64 (Reg.gpr 19#5) = x.bufRef → s4.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s4.readReg64 (Reg.gpr 21#5) = x.slot → s4.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s4.readReg64 (Reg.gpr 23#5) = 1#64 → s4.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
        s4.readReg64 (Reg.gpr 25#5) = 8#64 → s4.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 after1.length →
        ChunkedInl10CalleeSaved s0 s4 →
        SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s4
          (e2b302_domUcPreZeroDk A lim st evsAuth s0 s4 x.msgPtr x.bufRef x.slot x.ptr
            u.epoch u.auth none none x.bs after_auth)
          (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
          (WppPanicFalse R) by
      dsimp only [after_ep] at hafter_ep_le hafter_ep_suf ⊢
      cases hauth : u.auth with
      | none =>
        rw [hauth] at hafter_ep_le hafter_ep_suf h_after_auth
        dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
          at hafter_ep_le hafter_ep_suf ⊢
        exact h_after_auth [] s3 (.nil _ _ _) hafter_ep_le hafter_ep_suf
          hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hcs3
      | some authPb =>
        have hValid_auth : tlb_ValidAuthPB authPb := hValid_auth_opt authPb hauth
        rw [hauth] at hafter_ep_le hafter_ep_suf h_after_auth
        rw [e2b302_encodeOptMessage_auth_tag2_some authPb after_auth] at hafter_ep_le hafter_ep_suf ⊢
        let rest_a := tlb_lenPrefixed (ProtoAuthenticator.encodeRaw authPb) after_auth
        have hauth_gt : ¬ (0x12#8 :: rest_a).length ≤ after1.length := by
          have hgt_a := e2b302_lenPrefixed_length_gt (ProtoAuthenticator.encodeRaw authPb) after_auth
          dsimp only [rest_a, after_auth] at hgt_a ⊢
          simp only [List.length_cons, List.length_append] at hgt_a ⊢
          omega
        have hd_12 := e2b302_decodeVarint_0x12 rest_a
        refine e2b302_dom_uc_decode_key hVarintCall hauth_gt hsp_align hbs_lt hafter_ep_le hafter_ep_suf
          hd_12 (by decide) (by decide : WireType.ofNat? ((0x12#64).toNat % 8) = some .lengthDelimited)
          (by decide) ?_ hpc3 hrun3 hsp3 htr3
          hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hcs3
        intro s3' ha_rest_le ha_rest_suf hpc3' hrun3' hsp3' htr3' hx0_3' hx1_3'
          hx19_3' hx20_3' hx21_3' hx22_3' hx23_3' hx24_3' hx25_3' hx26_3' hcs3'
        have hx1_3'' : s3'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 2 := by
          have hk : BitVec.ofNat 64 ((0x12#64).toNat / 8) = BitVec.ofNat 64 2 := by decide
          rwa [hk] at hx1_3'
        exact e2b302_dom_uc_auth_step hOps hCum hReq hAuthTightCall hFit (.nil 0 0 0)
          hValid_auth rfl hsp_align hbs_lt ha_rest_le ha_rest_suf h_after_auth
          hpc3' hrun3' hsp3' htr3' hx0_3' hx1_3''
          hx19_3' hx20_3' hx21_3' hx22_3' hx23_3' hx24_3' hx25_3' hx26_3' hcs3'
    intro evsAuth s4 hA hafter_auth_le hafter_auth_suf hpc4 hrun4 hsp4 htr4
      hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hcs4
    dsimp only [after_auth] at hafter_auth_le hafter_auth_suf ⊢
    cases hdk : u.dk with
    | nil =>
      rw [hdk] at hafter_auth_le hafter_auth_suf
      dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField,
        List.isEmpty_nil, ↓reduceIte, List.nil_append] at hafter_auth_le hafter_auth_suf ⊢
      have hu_eq : ({ epoch := u.epoch, auth := u.auth, dk := [] } : V1State.Unchunked.EkSent) = u := by
        cases u; dsimp only at hdk ⊢; subst hdk; rfl
      apply SepWPpLscro.weaken_pre
        (e2b302_zeroDk_entails_ucLoopPre A lim st evsAuth s0 s4 x.msgPtr x.bufRef x.slot x.ptr
          u.epoch u.auth none none x.bs after1)
      rw [hu_eq]
      refine e2b302_dom_uc_exit rfl hafter_auth_le hafter_auth_suf ?_
        hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hcs4
      intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hcs5
      have happ_nil : evsAuth = evsAuth ++ [] := (List.append_nil evsAuth).symm
      rw [happ_nil]
      exact hcont evsAuth [] s5 hA (.nil 2 19578 2560) hafter_auth_le hafter_auth_suf
        hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hcs5
    | cons b bs =>
      have hdk_len' : (b :: bs).length ≤ 2400 := by rwa [hdk] at hdk_len
      rw [hdk] at hafter_auth_le hafter_auth_suf
      rw [e2b302_encodeBytesField_tag3_nonempty b bs after1] at hafter_auth_le hafter_auth_suf ⊢
      let rest_dk := tlb_lenPrefixed (b :: bs) after1
      have hdk_gt : ¬ (0x1a#8 :: rest_dk).length ≤ after1.length := by
        have hgt_dk := e2b302_lenPrefixed_length_gt (b :: bs) after1
        dsimp only [rest_dk] at hgt_dk ⊢
        simp only [List.length_cons] at hgt_dk ⊢
        omega
      have hd_1a := e2b302_decodeVarint_0x1a rest_dk
      refine e2b302_dom_uc_decode_key hVarintCall hdk_gt hsp_align hbs_lt hafter_auth_le hafter_auth_suf
        hd_1a (by decide) (by decide : WireType.ofNat? ((0x1a#64).toNat % 8) = some .lengthDelimited)
        (by decide) ?_ hpc4 hrun4 hsp4 htr4
        hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hcs4
      intro s4' hdk_rest_le hdk_rest_suf hpc4' hrun4' hsp4' htr4' hx0_4' hx1_4'
        hx19_4' hx20_4' hx21_4' hx22_4' hx23_4' hx24_4' hx25_4' hx26_4' hcs4'
      have hx1_4'' : s4'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3 := by
        have hk : BitVec.ofNat 64 ((0x1a#64).toNat / 8) = BitVec.ofNat 64 3 := by decide
        rwa [hk] at hx1_4'
      refine e2b302_dom_uc_dk_step hOps hCum hReq hBytesCall hFit hA hdk_len' rfl
        hsp_align hbs_lt hdk_rest_le hdk_rest_suf ?_
        hpc4' hrun4' hsp4' htr4' hx0_4' hx1_4''
        hx19_4' hx20_4' hx21_4' hx22_4' hx23_4' hx24_4' hx25_4' hx26_4' hcs4'
      intro evsDk s5 hDk hafter1_le hafter1_suf hpc5 hrun5 hsp5 htr5
        hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hcs5
      have hu_eq : ({ epoch := u.epoch, auth := u.auth, dk := b :: bs } : V1State.Unchunked.EkSent) = u := by
        cases u; dsimp only at hdk ⊢; subst hdk; rfl
      rw [hu_eq]
      refine e2b302_dom_uc_exit rfl hafter1_le hafter1_suf ?_
        hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hcs5
      intro s6 hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hcs6
      exact hcont evsAuth evsDk s6 hA hDk hafter1_le hafter1_suf
        hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hx21_6 hx22_6 hx23_6 hx24_6 hx25_6 hcs6

private theorem e2b302_dom_stage2_ek [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyEncTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evsAuth evsDk : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.EkSent} {ekOpt : Option PolynomialEncoder}
    {after2 : List (BitVec 8)} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hValid_ek : ∀ e, ekOpt = some e → tlb_ValidPolyEncoderPB e)
    (hafter_ge : outerLimit ≤ after2.length)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56) (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialEncoder.encodeRaw 2#32 ekOpt ++ after2).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialEncoder.encodeRaw 2#32 ekOpt ++ after2))
    (hcont : ∀ (evsEnc : List AllocEvent) (s' : State),
      SpqrTightEvs encOps encCum encReq evsEnc →
      after2.length ≤ x.bs.length → IsDropSuffix x.bs after2 →
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, sendingEk := ekOpt, receivingCt1 := none } x.bs after2)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st (evsAuth ++ evsDk) s0 s x.msgPtr x.bufRef x.slot x.ptr
        { uc := ucOpt, sendingEk := none, receivingCt1 := none } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          PolynomialEncoder.encodeRaw 2#32 ekOpt ++ after2))
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  cases ekOpt with
  | none =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
      at hcur_le hcur_suf ⊢
    have happ_nil : evsAuth ++ evsDk = evsAuth ++ evsDk ++ [] := (List.append_nil _).symm
    rw [happ_nil]
    exact hcont [] s (.nil _ _ _) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | some encPb =>
    have hValid_enc : tlb_ValidPolyEncoderPB encPb := hValid_ek encPb rfl
    rw [e2b302_encodeOptMessage_polyEnc_tag2_some encPb after2] at hcur_le hcur_suf ⊢
    let rest_ek := tlb_lenPrefixed (PolynomialEncoder.encodeRaw encPb) after2
    change (0x12#8 :: rest_ek).length ≤ x.bs.length at hcur_le
    change IsDropSuffix x.bs (0x12#8 :: rest_ek) at hcur_suf
    have hcur_gt : ¬ (0x12#8 :: rest_ek).length ≤ outerLimit := by
      have hgt_ek := e2b302_lenPrefixed_length_gt (PolynomialEncoder.encodeRaw encPb) after2
      dsimp only [rest_ek] at hgt_ek ⊢
      simp only [List.length_cons] at hgt_ek ⊢
      omega
    have hcur_lt : (0x12#8 :: rest_ek).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hd_12 := e2b302_decodeVarint_0x12 rest_ek
    have hrest_ek_le : rest_ek.length ≤ x.bs.length := by
      simp only [List.length_cons] at hcur_le; omega
    have hrest_ek_suf : IsDropSuffix x.bs rest_ek :=
      suffix_trans hcur_le hcur_suf (by simp only [List.length_cons]; omega)
        (decodeVarint_suffix hd_12)
    refine e2b302_dom_outer_decode_key hVarintCall hcur_gt hsp_align hcur_le hcur_lt hcur_suf
      hd_12 (by decide) (by decide : WireType.ofNat? ((0x12#64).toNat % 8) = some .lengthDelimited)
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    have hx1_1' : s1.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 2 := by
      have hk : BitVec.ofNat 64 ((0x12#64).toNat / 8) = BitVec.ofNat 64 2 := by decide
      rwa [hk] at hx1_1
    exact e2b302_dom_tag2_ek_step hOps hCum hReq hPolyEncTightCall hFit hA hDk
      rfl hValid_enc rfl hsp_align hbs_lt56 hbs_lt hrest_ek_le hrest_ek_suf hcont
      hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1

private theorem e2b302_dom_stage3_ct1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hPolyDecTightCall : subroutine_ok ((blkPC_302).rebase entry H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv))))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {evsAuth evsDk evsEnc : List AllocEvent}
    {R : SepProp} {s0 s : State}
    {ucOpt : Option V1State.Unchunked.EkSent} {ekOpt : Option PolynomialEncoder}
    {ct1Opt : Option PolynomialDecoder} {rest_final : List (BitVec 8)}
    (hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq))
    (hA : SpqrTightEvs authOps authCum authReq evsAuth)
    (hDk : SpqrTightEvs 2 19578 2560 evsDk)
    (hE : SpqrTightEvs encOps encCum encReq evsEnc)
    (hValid_ct1 : ∀ d, ct1Opt = some d → tlb_ValidPolyDecoderPB d)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt56 : x.bs.length < 2 ^ 56) (hbs_lt : x.bs.length < 2 ^ 63)
    (hcur_le : (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
      PolynomialDecoder.encodeRaw 3#32 ct1Opt ++ rest_final).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
        PolynomialDecoder.encodeRaw 3#32 ct1Opt ++ rest_final))
    (hcont : ∀ (evsDec : List AllocEvent) (s' : State),
      SpqrTightEvs decOps decCum decReq evsDec →
      rest_final.length ≤ x.bs.length → IsDropSuffix x.bs rest_final →
      s'.pc = entry + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_final.length →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s'
        (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc ++ evsDec) s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { uc := ucOpt, sendingEk := ekOpt, receivingCt1 := ct1Opt } x.bs rest_final)
        (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
        (WppPanicFalse R))
    (hpc : s.pc = entry + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_final.length)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase entry H) (s0.readReg64 Reg.lr) s
      (e2b302_domLoopPre A lim st (evsAuth ++ evsDk ++ evsEnc) s0 s x.msgPtr x.bufRef x.slot x.ptr
        { uc := ucOpt, sendingEk := ekOpt, receivingCt1 := none } x.bs
        (CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
          PolynomialDecoder.encodeRaw 3#32 ct1Opt ++ rest_final))
      (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0)
      (WppPanicFalse R) := by
  cases ct1Opt with
  | none =>
    dsimp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage, List.nil_append]
      at hcur_le hcur_suf ⊢
    have happ_nil : evsAuth ++ evsDk ++ evsEnc = evsAuth ++ evsDk ++ evsEnc ++ [] :=
      (List.append_nil _).symm
    rw [happ_nil]
    exact hcont [] s (.nil _ _ _) hcur_le hcur_suf
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | some decPb =>
    have hValid_dec : tlb_ValidPolyDecoderPB decPb := hValid_ct1 decPb rfl
    rw [e2b302_encodeOptMessage_polyDec_tag3_some decPb rest_final] at hcur_le hcur_suf ⊢
    let rest_ct1 := tlb_lenPrefixed (PolynomialDecoder.encodeRaw decPb) rest_final
    change (0x1a#8 :: rest_ct1).length ≤ x.bs.length at hcur_le
    change IsDropSuffix x.bs (0x1a#8 :: rest_ct1) at hcur_suf
    have hcur_gt : ¬ (0x1a#8 :: rest_ct1).length ≤ rest_final.length := by
      have hgt_ct1 := e2b302_lenPrefixed_length_gt (PolynomialDecoder.encodeRaw decPb) rest_final
      dsimp only [rest_ct1] at hgt_ct1 ⊢
      simp only [List.length_cons] at hgt_ct1 ⊢
      omega
    have hcur_lt : (0x1a#8 :: rest_ct1).length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
    have hd_1a := e2b302_decodeVarint_0x1a rest_ct1
    have hrest_ct1_le : rest_ct1.length ≤ x.bs.length := by
      simp only [List.length_cons] at hcur_le; omega
    have hrest_ct1_suf : IsDropSuffix x.bs rest_ct1 :=
      suffix_trans hcur_le hcur_suf (by simp only [List.length_cons]; omega)
        (decodeVarint_suffix hd_1a)
    refine e2b302_dom_outer_decode_key hVarintCall hcur_gt hsp_align hcur_le hcur_lt hcur_suf
      hd_1a (by decide) (by decide : WireType.ofNat? ((0x1a#64).toNat % 8) = some .lengthDelimited)
      (by decide) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
    have hx1_1' : s1.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 3 := by
      have hk : BitVec.ofNat 64 ((0x1a#64).toNat / 8) = BitVec.ofNat 64 3 := by decide
      rwa [hk] at hx1_1
    exact e2b302_dom_tag3_ct1_step hOps hCum hReq hPolyDecTightCall hFit hA hDk hE
      rfl hValid_dec rfl hsp_align hbs_lt56 hbs_lt hrest_ct1_le hrest_ct1_suf hcont
      hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1

end DomOnlyProof

private theorem e2b302_dom_only_subroutine_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    (hPolyEncTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    (hPolyDecTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)))) :
    subroutine_ok ((blkPC_302).rebase (blkPl_302).base H)
      (blkPl_302).base
      (withLsCodeRoLoaded lsmpl (e2b302_domOnlySpec A lim maxOps cumCap maxReq)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2b302_domOnlySpec chunkedHeaderSentMergeSpecOfEnv
  apply ProofLib.subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim; intro hDom
  apply sepWPpLscro_pure_elim; rintro ⟨h_1, h_2, h_3, _hbound_ek, hbound_ct1, hFit_guard⟩
  obtain ⟨hwt_proto, hmsg_def, pb, rest_final, ⟨hValid_uc, hValid_ek, hValid_ct1⟩, hbs_eq⟩ := id hDom
  have hbs_lt56 : x.bs.length < 2 ^ 56 := by unfold OptPolyDecoderBound at hbound_ct1; omega
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have hwt_ld : x.wt = .lengthDelimited := e2b302_wt_eq_lengthDelimited hwt_proto
  have hFit : FitsEnv M lim st (SpqrTightEvs maxOps cumCap maxReq) :=
    fun evs ht => hFit_guard evs (Or.inl ⟨hDom, ht⟩)
  let raw_hs := V1State.Chunked.HeaderSent.encodeRaw pb
  have hdv0 : decodeVarint x.bs = some (BitVec.ofNat 64 raw_hs.length, raw_hs ++ rest_final) := by
    rw [hbs_eq]; exact e2b302_lenPrefixed_decodeVarint raw_hs rest_final
  have hgt_hs : raw_hs.length + rest_final.length < x.bs.length := by
    rw [hbs_eq]; exact e2b302_lenPrefixed_length_gt raw_hs rest_final
  have hraw_hs_lt64 : raw_hs.length < 2 ^ 64 := by omega
  have hlen_hs : (BitVec.ofNat 64 raw_hs.length).toNat = raw_hs.length := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_hs_lt64]
  have hlt_len : ¬ (raw_hs ++ rest_final).length < (BitVec.ofNat 64 raw_hs.length).toNat := by
    rw [hlen_hs, List.length_append]; omega
  have houter_lim : (raw_hs ++ rest_final).length - (BitVec.ofNat 64 raw_hs.length).toNat = rest_final.length := by
    rw [hlen_hs, List.length_append]; omega
  have hsome_hs : (mergeMessage V1State.Chunked.HeaderSent.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (pb, rest_final) := by
    rw [hwt_proto, hmsg_def, hbs_eq]
    exact e2b302_mergeMessage_ch_headerSent pb rest_final hraw_hs_lt64
  have hrest0_le : (raw_hs ++ rest_final).length ≤ x.bs.length := by
    rw [List.length_append]; omega
  have hrest0_suf : IsDropSuffix x.bs (raw_hs ++ rest_final) := decodeVarint_suffix hdv0
  refine e2b302_dom_prologue hVarintCall hpc hrun hsp_align h_1 h_2 h_3
    hbs_lt hwt_ld hdv0 hlt_len ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [houter_lim] at hx22_1
  rw [hmsg_def]
  change SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s1
    (e2b302_domLoopPre A lim st [] s0 s1 x.msgPtr x.bufRef x.slot x.ptr
      { uc := none, sendingEk := none, receivingCt1 := none } x.bs (raw_hs ++ rest_final))
    (WppPost (e2b302_domOnlySpec A lim maxOps cumCap maxReq) (x, st) R s0) (WppPanicFalse R)
  have hsplit_hs := e2b302_headerSent_encodeRaw_split pb rest_final
  dsimp only [raw_hs] at hrest0_le hrest0_suf ⊢
  rw [hsplit_hs] at hrest0_le hrest0_suf ⊢
  let after2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    PolynomialDecoder.encodeRaw 3#32 pb.receivingCt1 ++ rest_final
  let after1 := CryptoVerification.LibsignalSpqrV1.Proto.encodeOptMessage
    PolynomialEncoder.encodeRaw 2#32 pb.sendingEk ++ after2
  have hafter2_ge : rest_final.length ≤ after2.length := by
    dsimp only [after2]; simp only [List.length_append]; omega
  have hafter1_ge : rest_final.length ≤ after1.length := by
    dsimp only [after1]; simp only [List.length_append]; omega
  refine e2b302_dom_stage1_uc hOps hCum hReq hVarintCall hBytesCall hAuthTightCall
    hFit hValid_uc hafter1_ge hsp_align hbs_lt hrest0_le hrest0_suf ?_
    hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  intro evsAuth evsDk s2 hA hDk hafter1_le hafter1_suf
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
  refine e2b302_dom_stage2_ek hOps hCum hReq hVarintCall hPolyEncTightCall
    hFit hA hDk hValid_ek hafter2_ge hsp_align hbs_lt56 hbs_lt hafter1_le hafter1_suf ?_
    hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hcs2
  intro evsEnc s3 hE hafter2_le hafter2_suf
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3
  refine e2b302_dom_stage3_ct1 hOps hCum hReq hVarintCall hPolyDecTightCall
    hFit hA hDk hE hValid_ct1 hsp_align hbs_lt56 hbs_lt hafter2_le hafter2_suf ?_
    hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hcs3
  intro evsDec s4 hD hrest_final_le hrest_final_suf
    hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 _hx23_4 _hx24_4 _hx25_4 hcs4
  have hpb_eq : ({ uc := pb.uc, sendingEk := pb.sendingEk, receivingCt1 := pb.receivingCt1 } :
      V1State.Chunked.HeaderSent) = pb := by cases pb; rfl
  rw [hpb_eq]
  exact e2b302_dom_ok_exit hDom hsp_align rfl hrest_final_le hrest_final_suf hsome_hs
    (e2b302_tight_combine hOps hCum hReq hA hDk hE hD)
    hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hx22_4 hcs4

/-! ## 4. Public Guarded-Tight Contracts for Block `302` -/

/-- Fully parametric Block `302` (`V1State.Chunked.HeaderSent::merge`) guarded-tight contract on
`(blkPC_302).rebase (blkPl_302).base H`. -/
theorem e2b302_chunkedHeaderSent_merge_blk_tight_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {authOps authCum authReq encOps encCum encReq decOps decCum decReq maxOps cumCap maxReq : Nat}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hCum : authCum + 19578 + encCum + decCum ≤ cumCap)
    (hReq : max (max authReq 2560) (max encReq decReq) ≤ maxReq)
    (hFromCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl
        (tlb_authMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv)
          (tlb_GuardedEnv tlb_AuthDom (SpqrTightEvs authOps authCum authReq) AuthMergeEnv))))
    (hPolyEncTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyEncoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyEncoderDom (SpqrTightEvs encOps encCum encReq) PolyEncoderMergeEnv))))
    (hPolyDecTightCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl
        (tlb_polyDecoderMergeTightSpecOfEnv A lim
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)
          (tlb_GuardedEnv tlb_PolyDecoderDom (SpqrTightEvs decOps decCum decReq) PolyDecoderMergeEnv)))) :
    subroutine_ok ((blkPC_302).rebase (blkPl_302).base H)
      (blkPl_302).base
      (withLsCodeRoLoaded lsmpl
        (chunkedHeaderSentMergeSpecOfEnv A lim
          (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq)
          (e2b302_ChunkedHeaderSentGuardedEnv maxOps cumCap maxReq))) := by
  have hDomOk := e2b302_dom_only_subroutine_ok hOps hCum hReq
    hVarintCall hBytesCall hAuthTightCall hPolyEncTightCall hPolyDecTightCall
  have hKleene := chunked_header_sent_merge_cl_placed_ok_of_contracts
    hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall hPolyEncCall hPolyDecCall
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : tlb_ChunkedHeaderSentDom x.1
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2b302_domOnlySpec A lim maxOps cumCap maxReq)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, e2b302_domOnlySpec]
      exact sepConj_mono_left (sepConj_mono_left (Entails.pure_right hDom (Entails.refl _)))
    exact hDomOk.mono_outcome x R s0 hpc hrun hpre_dom hsp fun _ out => out
  · have hpre_kl : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)).pre x s0 ∗ R := by
      refine Satisfies.mono ?_ hpre
      dsimp only [withLsCodeRoLoaded, chunkedHeaderSentMergeSpec, chunkedHeaderSentMergeSpecOfEnv,
        e2b302_ChunkedHeaderSentGuardedEnv, tlb_GuardedEnv]
      refine sepConj_mono_left (sepConj_mono_left ?_)
      refine Entails.pure_left fun hp =>
        Entails.pure_right ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, ?_⟩ (Entails.refl _)
      exact fun evs he => hp.2.2.2.2.2 evs (Or.inr ⟨hDom, he⟩)
    refine hKleene.mono_outcome x R s0 hpc hrun hpre_kl hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩)
    · refine Or.inl ⟨hret, hcc, Satisfies.mono ?_ hq⟩
      dsimp only [withLsCodeRoLoaded, chunkedHeaderSentMergeSpec, chunkedHeaderSentMergeSpecOfEnv,
        e2b302_ChunkedHeaderSentGuardedEnv, tlb_GuardedEnv]
      refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
      refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
      exact Entails.sepExists_right evs
        (Entails.pure_right (Or.inr ⟨hDom, chunkedHeaderSentMergePostEnv_imp_pre hevs⟩)
          (Entails.refl _))
    · dsimp only [withLsCodeRoLoaded, chunkedHeaderSentMergeSpec,
        chunkedHeaderSentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedHeaderSentMergeSpec,
        chunkedHeaderSentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1
    · dsimp only [withLsCodeRoLoaded, chunkedHeaderSentMergeSpec,
        chunkedHeaderSentMergeSpecOfEnv] at hq
      rw [satisfies_pure_sepConj] at hq
      exact False.elim hq.1

/-- Guarded-tight contract `tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim maxOps ext` on
`libsignalSessionLib.blockProgram lsmpl 302 (Rust.withPanics ext)` (`authOps + 2 + encOps + decOps ≤ maxOps`). -/
theorem e2b302_chunkedHeaderSentMerge_placed_tight_ok_of [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {authOps encOps decOps maxOps : Nat} {ext : String → Option (State → State)}
    (hOps : authOps + 2 + encOps + decOps ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim authOps ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim encOps ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim decOps ext) :
    tlb_ChunkedHeaderSentMergePlacedTightOkOf A lim maxOps ext := by
  have hFrom' := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFrom
  have hPush' := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPush
  have hVarint' := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint
  have hSkip' := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkip
  have hBytes' := e2b302_bytesMerge3_poly_of_signed hBytes
  have hok := e2b302_chunkedHeaderSent_merge_blk_tight_ok_of_contracts
    (H := Rust.withPanics ext)
    (authOps := authOps) (authCum := 2952) (authReq := 32)
    (encOps := encOps) (encCum := 342615) (encReq := 2560)
    (decOps := decOps) (decCum := 342615) (decReq := 2560)
    (maxOps := maxOps) (cumCap := 707760) (maxReq := 2560)
    hOps (by decide) (by decide)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_261).rebase (CryptoVerification.blkPl_261).base (fun _ => none))) hFrom')
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.RecordCodecs.Placed.blkPC_257).rebase (CryptoVerification.RecordCodecs.Placed.blkPl_257).base (fun _ => none))) hPush')
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_291).rebase (CryptoVerification.blkPl_291).base (fun _ => none))) hVarint')
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_263).rebase (CryptoVerification.blkPl_263).base (fun _ => none))) hSkip')
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_290).rebase (CryptoVerification.blkPl_290).base (fun _ => none))) hBytes')
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthBase)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncBase)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_296).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_296).base (fun _ => none))) hPolyDecBase)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.blkPC_295).rebase (CryptoVerification.blkPl_295).base (fun _ => none))) hAuthTight)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_297).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_297).base (fun _ => none))) hPolyEncTight)
    (e2b302_ls_subroutine_ok_cro_of_blockProgram_ext
      (IsLsBlockProg.externs_eq (prog := (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPC_296).rebase (CryptoVerification.SpqrV1.Prost.MessageMerge.blkPl_296).base (fun _ => none))) hPolyDecTight)
  rw [IsLsBlockProg.eq_blockProgram (prog := (blkPC_302).rebase (blkPl_302).base (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 302)] at hok
  exact hok

/-- Default `maxOps = 76` (`4 + 2 + 35 + 35`) specialization proving
`tlb_ChunkedHeaderSentMergePlacedTightOk`. -/
theorem e2b302_chunkedHeaderSentMerge_placed_tight_ok [LibsignalPlacement]
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
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hPolyEncBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296) (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hAuthTight : tlb_AuthMergePlacedTightOkOf A lim 4 ext)
    (hPolyEncTight : tlb_PolyEncoderMergePlacedTightOkOf A lim 35 ext)
    (hPolyDecTight : tlb_PolyDecoderMergePlacedTightOkOf A lim 35 ext) :
    tlb_ChunkedHeaderSentMergePlacedTightOk A lim ext :=
  e2b302_chunkedHeaderSentMerge_placed_tight_ok_of (Nat.le_refl 76)
    hFrom hPush hVarint hSkip hBytes hAuthBase hPolyEncBase hPolyDecBase
    hAuthTight hPolyEncTight hPolyDecTight

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.E2aTightB302PlacedBudget
