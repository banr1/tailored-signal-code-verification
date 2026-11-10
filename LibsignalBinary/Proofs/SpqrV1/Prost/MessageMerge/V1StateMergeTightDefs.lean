/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoop
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateLoopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProofClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Loop
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbChunked
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Guarded-Tight Shared Definitions and Canonical Loop Helpers for `V1State::merge` (Block `298`)

Shared infrastructure for guarded-tight allocator-budget verification of `V1State::merge`:
canonical-domain (`tlb_V1StateMergeDom`) vs fallback outcome splitting, cross-block callee lift
helpers, canonical protobuf roundtrip and 1-byte tag-key split lemmas across all 11 `V1State`
arms, and Block `298` prologue, epilogue, and jump-table dispatch steps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs

open Arm64 ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns
   libsignalSessionLib ls_subroutine_ok_cl_of_block ls_subroutine_ok_of_block lsmpl
   withLsCl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint decodeVarint_length)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeMessage encodeVarint mergeMessage)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix bv32_zeroExtend_ofNat decodeVarint_suffix key_shr32_of_lt key_wt_some
   pointsToBytes_prefix_join sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join
   sliceCursorAt suffix_trans tag_cbz_false ule_len_of_ge w1_tag_eq)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (InnerStateDiscrFull OptInnerStatePolyBound SepWPp.call_frame_lscro SepWPp.elim_lscroProp
   SepWPp.of_sepWP_lscro V1StateLoopRegsPlaced V1StateMergeGhost V1StateTagEntryHypPlaced WppPost
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedInlStack cmp_len_limit_of_eq
   cmp_len_limit_of_gt codecWireTypeToProto optInnerStatePolyBound_lt_2_56 optProtoInnerStateCapAt
   optProtoInnerStateCapAt_entails_discrFull optProtoInnerStateCapAt_mono
   stackAt_v1StateMerge_epilogue stackAt_v1StateMerge_prologue
   subroutine_ok_withLsCodeRoLoaded_of_withLscroProp v1Loop_discr_tail_entails_cap
   v1Proof_savedRegs_intro v1StateBelow_decodeVarint2 v1StateBelow_decodeVarint2_entails
   v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded v1StateMergeStack
   v1StateSavedRegsAt withLscroProp wt_beq_two_of_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_298 blkPl_298)
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge.Part2
open CryptoVerification.SpqrV1Sync.Codec
  (LoopsTo loopsTo_ch_ct1Acknowledged loopsTo_ch_ct1Received loopsTo_ch_ct1Sampled
   loopsTo_ch_ct2Sampled loopsTo_ch_ekReceivedCt1Sampled loopsTo_ch_ekSentCt1Received
   loopsTo_ch_headerReceived loopsTo_ch_headerSent loopsTo_ch_keysSampled
   loopsTo_ch_keysUnsampled loopsTo_ch_noHeaderReceived loopsTo_v1State mergeMessage_encode
   proto_decodeVarint_encodeVarint proto_encodeVarint_length proto_encodeVarint_of_lt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_V1StateMergeDom tlb_V1StateMergeGuardedEnvOf tlb_V1StateMergeTightEnvOf
   tlb_ValidV1StatePB tlb_fitsEnv_fallback_of_not_dom tlb_lenPrefixed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (V1StateMergeEnv v1StateLoopPrePlaced v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv
   v1StateMergePostEnv_imp_pre v1StateMergeSpec v1StateMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateTag1BudgetAux
  (WppPanicFalse stepEvents_append_eq wppPanicFalse_of_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv decodeVarintSliceEvents)

attribute [local irreducible] Program.fetch Program.externAt?
  optProtoInnerStateJumpTablePlacedAt v1StateSavedRegsAt
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_beq_zero
  CryptoVerification.SpqrV1.ProtoRepr.EncodedLen.noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

private theorem e2m_key_tag_le_11 {key : BitVec 64} (h : key.toNat / 8 ≤ 11) :
    (BitVec.ule 96#64 key) = false ∧ (BitVec.ult key 96#64) = true := by
  have hlt : key.toNat < 96 := by omega
  simp only [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not]
  change ¬ 96 ≤ key.toNat ∧ key.toNat < 96
  omega

private theorem e2m_decodeVarint2Env_eq_nil {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = some (v, rest)) (h : DecodeVarint2Env bs evs) :
    evs = [] := by
  simpa only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd] using h

/-! ## 1. `Dom`-Gated Contract & `Dom` / `¬ Dom` Outcome Split -/

/-- Bundled canonical-domain + tight `FitsEnv` precondition conjunct (kept as a structure so
`wpp_init` preserves a 6-conjunct pure precondition). -/
structure E2mDomFit (M : AllocCostModel) (lim : BudgetLimits) (maxOps : Nat)
    (x : V1StateMergeGhost) (st : M.σ) : Prop where
  dom : tlb_V1StateMergeDom x
  fit : FitsEnv M lim st (tlb_V1StateMergeTightEnvOf maxOps)

/-- Canonical-domain-only `Spec` for `Block 298`: requires `E2mDomFit M lim maxOps x st` in `pre`
and shares the exact `post` / `onPanic` / `onExit` / `onOom` of
`v1StateMergePlacedSpecOfEnv A lim (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps)`. -/
def e2mDomSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat) :
    Spec (V1StateMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
      E2mDomFit M lim maxOps x st⌝ ∗
      optProtoInnerStateCapAt A.repAlloc x.msgPtr x.bs.length x.msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp v1StateMergeStack
  post := (v1StateMergePlacedSpecOfEnv A lim
    (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps)).post

/-- Combines a `tlb_V1StateMergeDom`-only tight contract `hDomOk` with the existing untightened
`v1StateMergePlacedSpec` contract `hFallback` (`¬ tlb_V1StateMergeDom`) into the full guarded-tight
contract `v1StateMergePlacedSpecOfEnv A lim (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps)`. -/
theorem e2m_subroutine_ok_of_dom_and_fallback [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {prog : Program} {entry : BitVec 64}
    (hDomOk : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (e2mDomSpec A lim maxOps)))
    (hFallback : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (v1StateMergePlacedSpecOfEnv A lim
          (tlb_V1StateMergeGuardedEnvOf maxOps) (tlb_V1StateMergeGuardedEnvOf maxOps))) := by
  apply subroutine_ok_intro
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align
  by_cases hDom : tlb_V1StateMergeDom x
  · have hpre_dom : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (e2mDomSpec A lim maxOps)).pre (x, st0) s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded, e2mDomSpec, v1StateMergePlacedSpecOfEnv] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      refine Entails.pure_left fun hp => ?_
      have hv :
          (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
            s0.readReg64 .x1 = x.msgPtr ∧
            s0.readReg64 .x2 = x.bufRef ∧
            x.bs.length < 2 ^ 63 ∧
            OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
            E2mDomFit M lim maxOps x st0 :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          ⟨hDom, fun evs ht => hp.2.2.2.2.2 evs (Or.inl ⟨hDom, ht⟩)⟩⟩
      simp only [eq_true hv, pure_true, emp_sepConj]
      exact Entails.refl _
    exact subroutine_ok_apply_full hDomOk (x, st0) R hpc hrun hpre_dom hsp_align
  · have hpre_fb : s0.mem ⊨ (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)).pre (x, st0) s0 ∗ R := by
      dsimp only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv] at hpre ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
      refine Entails.pure_left fun hp => ?_
      have hv :
          (s0.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
            s0.readReg64 .x1 = x.msgPtr ∧
            s0.readReg64 .x2 = x.bufRef ∧
            x.bs.length < 2 ^ 63 ∧
            OptInnerStatePolyBound x.bs.length x.msg.innerState ∧
            FitsEnv M lim st0 (V1StateMergeEnv x) :=
        ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
          tlb_fitsEnv_fallback_of_not_dom hDom hp.2.2.2.2.2⟩
      simp only [eq_true hv, pure_true, emp_sepConj]
      exact Entails.refl _
    refine reaches_pc_mono
      (subroutine_ok_apply_full hFallback (x, st0) R hpc hrun hpre_fb hsp_align)
      (fun sf _ _ ⟨hpostR, hcc⟩ => ⟨?_, hcc⟩)
    dsimp only [withLsCodeRoLoaded, v1StateMergePlacedSpec, v1StateMergePlacedSpecOfEnv,
      v1StateMergeSpecOfEnv, v1StateMergeSpec] at hpostR ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hpostR
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    refine Arm64.Entails.sepExists_elim fun evs => Arm64.Entails.pure_left fun hevs => ?_
    refine Arm64.Entails.sepExists_right evs ?_
    have hpe : tlb_V1StateMergeGuardedEnvOf maxOps x evs :=
      Or.inr ⟨hDom, v1StateMergePostEnv_imp_pre hevs⟩
    simp only [eq_true hpe, pure_true, emp_sepConj]
    exact Entails.refl _

/-- `SpqrTightEvs` closure under `FreeOnlyEvs` append. -/
theorem e2m_spqrTightEvs_append_freeOnly_defs {maxOps cumCap maxReq : Nat}
    {evs evs_d : List AllocEvent}
    (h : SpqrTightEvs maxOps cumCap maxReq evs) (hf : FreeOnlyEvs evs_d) :
    SpqrTightEvs maxOps cumCap maxReq (evs ++ evs_d) :=
  (h.append (SpqrTightEvs.of_freeOnly hf)).mono (by omega) (by omega) (by omega)

/-- Cross-block `withLsCodeLoaded` callee lift onto `callerProg`. -/
theorem e2m_ls_subroutine_ok_of_block_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeLoaded lsmpl spec) :=
  @ls_subroutine_ok_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-- Cross-block `withLsCl` callee lift onto `callerProg`. -/
theorem e2m_ls_subroutine_ok_cl_of_block_ext [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  @ls_subroutine_ok_cl_of_block _ _ callerProg
    (libsignalSessionLib.blockProgram lsmpl j H) i j H hcaller ⟨rfl, hext_j⟩ entry spec
    hcallee _ _ _ _ hi hj hj_unmut

/-- Cross-block `withLsCodeRoLoaded` callee lift onto `callerProg`. -/
theorem e2m_ls_subroutine_ok_cro_of_block_ext [LibsignalPlacement] {α : Type}
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

/-! ## 2. Pure Canonical Protobuf Roundtrip & 1-Byte Tag-Key Split Lemmas -/

theorem e2m_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt
  all_goals first | rfl | cases h

theorem e2m_v1State_eq_default_of_none {m : V1State} (h : m.innerState = none) :
    m = default := by
  cases m with
  | mk is =>
    simp only at h
    subst h
    rfl

theorem e2m_lenPrefixed_assoc (raw rest : List (BitVec 8)) :
    tlb_lenPrefixed raw rest = encodeVarint (BitVec.ofNat 64 raw.length) ++ (raw ++ rest) :=
  List.append_assoc _ _ _

theorem e2m_lenPrefixed_bounds {raw rest : List (BitVec 8)}
    (hlt : (tlb_lenPrefixed raw rest).length < 2 ^ 63) :
    raw.length < 2 ^ 63 ∧ raw.length < 2 ^ 64 ∧ rest.length < 2 ^ 63 ∧
      (raw ++ rest).length < (tlb_lenPrefixed raw rest).length := by
  have hvl := (proto_encodeVarint_length (BitVec.ofNat 64 raw.length)).1
  simp only [tlb_lenPrefixed, List.length_append] at hlt ⊢
  omega

theorem e2m_decodeVarint_lenPrefixed (raw rest : List (BitVec 8)) :
    decodeVarint (tlb_lenPrefixed raw rest) =
      some (BitVec.ofNat 64 raw.length, raw ++ rest) := by
  rw [← proto_decodeVarint_toOption, e2m_lenPrefixed_assoc, proto_decodeVarint_encodeVarint]
  rfl

theorem e2m_v1State_mergeMessage_canonical {wt : WireType} {msg pb : V1State}
    {rest : List (BitVec 8)}
    (hwt : codecWireTypeToProto wt = .lengthDelimited)
    (hm : msg.innerState = none)
    (hlen : (V1State.encodeRaw pb).length < 2 ^ 64) :
    (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg
      (tlb_lenPrefixed (V1State.encodeRaw pb) rest) 100).toOption = some (pb, rest) := by
  rw [hwt, e2m_v1State_eq_default_of_none hm, e2m_lenPrefixed_assoc,
      mergeMessage_encode V1State.mergeField 3 V1State.encodeRaw default pb 100 rest
        (loopsTo_v1State pb hlen) hlen (by decide)]
  rfl

theorem e2m_chunked_mergeMessage_canonical {N : Type} [Inhabited N]
    (mfN : N → BitVec 32 → CryptoVerification.LibsignalSpqrV1.Proto.WireType →
      List (BitVec 8) → Nat →
      Except CryptoVerification.LibsignalSpqrV1.Proto.DecodeErr (N × List (BitVec 8)))
    (encodeRawK : N → List (BitVec 8)) (ck : N) (rest : List (BitVec 8))
    (hlen : (encodeRawK ck).length < 2 ^ 64)
    (hloops : LoopsTo mfN 2 default (encodeRawK ck) ck) :
    (mergeMessage mfN .lengthDelimited default
      (tlb_lenPrefixed (encodeRawK ck) rest) 99).toOption = some (ck, rest) := by
  rw [e2m_lenPrefixed_assoc,
      mergeMessage_encode mfN 2 encodeRawK default ck 99 rest hloops hlen (by decide)]
  rfl

/-- Splits `encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest` (`k ∈ {1..11}`) into its
1-byte tag/wire-type varint `BitVec.ofNat 64 (8 * k + 2)` followed by
`tlb_lenPrefixed (encodeRawK ck) rest`. -/
theorem e2m_encodeMessage_split {N : Type} (encodeRawK : N → List (BitVec 8))
    (k : Nat) (ck : N) (rest : List (BitVec 8))
    (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
          k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11)
    (hlen : (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck).length < 2 ^ 63) :
    let cur := encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest
    let rest_k := tlb_lenPrefixed (encodeRawK ck) rest
    (encodeRawK ck).length < 2 ^ 64 ∧
    rest.length < cur.length ∧
    decodeVarint cur = some (BitVec.ofNat 64 (8 * k + 2), rest_k) ∧
    ¬ (2 ^ 32 ≤ (BitVec.ofNat 64 (8 * k + 2)).toNat) ∧
    WireType.ofNat? ((BitVec.ofNat 64 (8 * k + 2)).toNat % 8) = some .lengthDelimited ∧
    (BitVec.ofNat 64 (8 * k + 2)).toNat / 8 = k ∧
    (BitVec.ofNat 64 (8 * k + 2)).toNat / 8 ≤ 11 ∧
    ¬ ((BitVec.ofNat 64 (8 * k + 2)).toNat / 8 < 1) := by
  have hk_bytes :
      CryptoVerification.LibsignalSpqrV1.Proto.encodeKey (BitVec.ofNat 32 k) .lengthDelimited =
        [BitVec.ofNat 8 (8 * k + 2)] := by
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hk_ev :
      encodeVarint (BitVec.ofNat 64 (8 * k + 2)) = [BitVec.ofNat 8 (8 * k + 2)] := by
    rw [proto_encodeVarint_of_lt (BitVec.ofNat 64 (8 * k + 2))
      (by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have henc_eq :
      encodeMessage encodeRawK (BitVec.ofNat 32 k) ck =
        [BitVec.ofNat 8 (8 * k + 2)] ++
          (encodeVarint (BitVec.ofNat 64 (encodeRawK ck).length) ++ encodeRawK ck) := by
    simp only [encodeMessage, hk_bytes, List.append_assoc]
  have hcur_eq :
      encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest =
        encodeVarint (BitVec.ofNat 64 (8 * k + 2)) ++ tlb_lenPrefixed (encodeRawK ck) rest := by
    rw [henc_eq, hk_ev]
    simp only [tlb_lenPrefixed, List.append_assoc]
  have hvl := (proto_encodeVarint_length (BitVec.ofNat 64 (encodeRawK ck).length)).1
  have hlen_sub : (encodeRawK ck).length < 2 ^ 64 := by
    rw [henc_eq] at hlen
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  have hgt_rest :
      rest.length < (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest).length := by
    rw [henc_eq]
    simp only [List.length_append, List.length_singleton]
    omega
  have hdv :
      decodeVarint (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest) =
        some (BitVec.ofNat 64 (8 * k + 2), tlb_lenPrefixed (encodeRawK ck) rest) := by
    rw [hcur_eq, ← proto_decodeVarint_toOption, proto_decodeVarint_encodeVarint]
    rfl
  refine ⟨hlen_sub, hgt_rest, hdv, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 3. Canonical Block `298` Epilogue, Key-Jump Dispatch, & Prologue Helpers -/

private def e2mPlacedFixedPost [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : V1StateMergeGhost) (st0 : M.σ)
    (evs : List AllocEvent) (s0 sf : State) : SepProp :=
  ⌜sf.trace = s0.trace⌝ ∗ v1StateJumpTablesPlacedAt ∗ (x.bufRef ↦₆₄ x.slot) ∗
    A.pool lim (M.stepEvents evs st0) sf ∗
    stackAt s0.sp v1StateMergeStack ∗
    match (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption with
    | some (m', rest) =>
      ⌜sf.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
        optProtoInnerStateCapAt A.repAlloc x.msgPtr rest.length m'.innerState ∗
        sliceCursorAfter x.slot x.ptr x.bs rest
    | none =>
      ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗
        (∃∗ n : Nat, ⌜n ≤ 4⌝ ∗ CryptoVerification.LibsignalTripleRatchet.decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n) ∗
        (∃∗ is' : Option V1State.InnerState, CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc x.msgPtr is') ∗
        memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

private theorem e2m_postEnv_entails {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {maxOps : Nat} {x : V1StateMergeGhost} {st0 : M.σ} {sf : State}
    {evs : List AllocEvent}
    (hDom : tlb_V1StateMergeDom x) (htight : tlb_V1StateMergeTightEnvOf maxOps evs) :
    A.pool lim (M.stepEvents evs st0) sf ⊢
      ∃∗ evs' : List AllocEvent,
        ⌜tlb_V1StateMergeGuardedEnvOf maxOps x evs'⌝ ∗ A.pool lim (M.stepEvents evs' st0) sf := by
  refine Entails.sepExists_right evs ?_
  have hpost : tlb_V1StateMergeGuardedEnvOf maxOps x evs := Or.inl ⟨hDom, htight⟩
  simp only [eq_true hpost, pure_true, emp_sepConj]
  exact Entails.refl _

private theorem e2m_sepWP_wppPost_of_fixedPost [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {prog : Program} {s0 s : State}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R Pre : SepProp}
    (hDom : tlb_V1StateMergeDom x) (htight : tlb_V1StateMergeTightEnvOf maxOps evs)
    (h : SepWP prog (s0.readReg64 Reg.lr) s Pre
      (fun sf Pf =>
        ((sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ e2mPlacedFixedPost A lim x st0 evs s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)) :
    SepWP prog (s0.readReg64 Reg.lr) s Pre
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) := by
  refine SepWP.mono h fun sf Pf _ _ ⟨hm, hsp, hcs⟩ => ⟨fun hPf => ?_, hsp, hcs⟩
  refine Satisfies.mono (sepConj_mono_left ?_) (hm hPf)
  unfold e2mPlacedFixedPost e2mDomSpec v1StateMergePlacedSpecOfEnv
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (e2m_postEnv_entails A lim hDom htight))))

/-- Canonical success epilogue return at `+128` (`x1 = 0#64`) under `tlb_V1StateMergeTightEnvOf maxOps`. -/
theorem e2m_ok_ret_exit_128_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R : SepProp}
    {s0 s : State} {m' : V1State} {rest : List (BitVec 8)}
    (hDom : tlb_V1StateMergeDom x)
    (hsome : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
      some (m', rest))
    (htight : tlb_V1StateMergeTightEnvOf maxOps evs)
    (hbound : OptInnerStatePolyBound rest.length m'.innerState)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_298).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hx1 : s.readReg64 (Reg.gpr 1#5) = 0#64) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  rcases htr with ⟨htr, hvregs⟩
  apply SepWPp.of_sepWP_ret
  refine e2m_sepWP_wppPost_of_fixedPost hDom htight ?_
  dsimp only [e2mPlacedFixedPost]
  conv => arg 5; simp only [hsome]
  conv =>
    arg 4
    simp only [v1StateLoopPrePlaced, v1StateSavedRegsAt, sepConj_assoc, arm64_norm, htr, hsp, hx1]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  apply SepWP.fold (stackAt_v1StateMerge_epilogue s0.sp s0) (by unfold v1StateSavedRegsAt; sep_focus)
  wp_done

/-- Canonical loop exit at `+216` when `cur = rest` (`limit = rest.length`). -/
theorem e2m_ok_exit_216_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs : List AllocEvent} {R : SepProp}
    {s0 s : State} {m' : V1State} {rest : List (BitVec 8)}
    (hDom : tlb_V1StateMergeDom x)
    (hsome : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
      some (m', rest))
    (htight : tlb_V1StateMergeTightEnvOf maxOps evs)
    (hbound : OptInnerStatePolyBound rest.length m'.innerState)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64)
    (htr : s.v1TraceEq s0) (hregs : V1StateLoopRegsPlaced s0 x rest.length s) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim (M.stepEvents evs st0) s0 s x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨_hx19, _hx20, _hx22, _hx23, _hx24, _hx25, hx26, _hx27, hx28, _hx29⟩
  obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq (rfl : rest.length = rest.length)
  apply SepWPp.of_sepWP (mid := (blkPl_298).base + 128#64)
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt]
    simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_298).base + 128#64)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  wp_reach
  apply SepWPp.weaken_pre
    (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, sliceCursorAfter]; sep_ac_rfl))
  exact e2m_ok_ret_exit_128_placed hDom hsome htight hbound hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp])
    (by simp only [arm64_norm, htr]) (by simp only [arm64_norm])

/-- Canonical loop latch + exit (`+2700 → +216 → +128 → lr`) when the single arm finishes at
`rest' = rest` (`limit = rest.length`) with `x21 = 0#64`. -/
theorem e2m_latch_2700_ok_exit_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 : M.σ} {evs_tag : List AllocEvent} {R : SepProp}
    {s0 s' : State} {m' : V1State} {rest : List (BitVec 8)}
    (hDom : tlb_V1StateMergeDom x)
    (hsome : (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
      some (m', rest))
    (htight : tlb_V1StateMergeTightEnvOf maxOps evs_tag)
    (hbound : OptInnerStatePolyBound rest.length m'.innerState)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpc : s'.pc = (blkPl_298).base + 2700#64)
    (hrun : s'.status = .Running) (hsp : s'.sp = s0.sp - 816#64)
    (htr : s'.v1TraceEq s0) (hx21 : s'.readReg64 (Reg.gpr 21#5) = 0#64)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s')
    (hinv : LibsignalCodeRoLoaded lsmpl s'.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
      (v1StateLoopPrePlaced A lim (M.stepEvents evs_tag st0) s0 s' x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinv ?_
  conv => arg 4; rw [v1StateLoopPrePlaced]
  wp_steps_sync_pool ((blkPl_298).base + 216#64); wp_reach; intro _hinv'
  apply SepWPp.weaken_pre
    (P' := v1StateLoopPrePlaced A lim (M.stepEvents evs_tag st0) s0 _
      x.msgPtr x.bufRef x.slot x.ptr m' x.bs rest)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced]; sep_ac_rfl))
  exact e2m_ok_exit_216_placed hDom hsome htight hbound hsp_align hrest_le hrest_suf
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
     by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
     by simp only [arm64_norm, hx29]⟩

meta section
open Lean Meta Elab Tactic in
elab "e2m_wp_steps_sync_pool_target" : tactic => do
  let g ← getMainGoal
  let midStx ← g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    Lean.Elab.Term.exprToSyntax (ty.getArg! 1)
  evalTactic (← `(tactic| wp_steps_sync_pool $midStx))
end

set_option maxHeartbeats 1600000 in
private theorem e2m_jump_arm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    {x : V1StateMergeGhost} {st0 st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State} {rest_k : List (BitVec 8)} {iwt : WireType} {key : BitVec 64} {limit : Nat}
    {k : Nat} {off : BitVec 64}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest_k.length ≤ x.bs.length) (hrest_lt : rest_k.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest_k) (hbound : OptInnerStatePolyBound rest_k.length m.innerState)
    (hk_le : key.toNat / 8 ≤ 11)
    (htag_k : key.toNat / 8 = k)
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (harm : ∀ s' : State, V1StateTagEntryHypPlaced H s0 x m rest_k iwt limit s' →
      s'.pc = (blkPl_298).base + off →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest_k)
        (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = key)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 (key.toNat / 8))
    (hregs : V1StateLoopRegsPlaced s0 x limit s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest_k)
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hule96, hult96⟩ := e2m_key_tag_le_11 hk_le
  rw [htag_k] at hx8
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + off) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]
    simp only [sepConj_assoc]
  apply SepWP.fold (optProtoInnerStateCapAt_entails_discrFull A.repAlloc x.msgPtr rest_k.length m.innerState)
    (by sep_focus)
  conv => arg 4; rw [sepExists_sepConj_left]; simp only [sepConj_assoc]
  apply SepWP.exists_elim; intro d
  apply SepWP.pure_elim; intro hd
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> {
    e2m_wp_steps_sync_pool_target
    apply SepWP.fold (v1Loop_discr_tail_entails_cap A.repAlloc x.msgPtr rest_k.length m.innerState d hd) (by sep_focus)
    wp_reach; intro hinv'
    apply SepWPp.weaken_pre
      (P' := v1StateLoopPrePlaced A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest_k)
      (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, v1StateJumpTablesPlacedAt, v1StateMergeJumpTablePlacedExpanded]; sep_ac_rfl))
    exact harm _ ⟨hsp_align, hrest_le, hrest_lt, hrest_suf, hbound,
      by simp only [arm64_norm, hrun], by simp only [arm64_norm, hsp], by simp only [arm64_norm, htr],
      by simp only [arm64_norm, hx0], by simp only [arm64_norm]; exact hd,
      ⟨by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx22],
       by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hx29]⟩, hinv'⟩ (by simp only [arm64_norm])
  }

/-- Canonical key-decode + jump-table dispatch (`+216 → +236 → +268 → +off`) for
`cur = encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest` (`k ∈ {1..11}`). -/
theorem e2m_decode_key_jump_arm_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : V1StateMergeGhost} {st0 : M.σ} {R : SepProp} {s0 s : State}
    {N : Type} (encodeRawK : N → List (BitVec 8)) (ck : N) (rest : List (BitVec 8))
    {k : Nat} {off : BitVec 64}
    (hk_cases : k = 1 ∧ off = 300#64 ∨ k = 2 ∧ off = 564#64 ∨ k = 3 ∧ off = 428#64 ∨
      k = 4 ∧ off = 476#64 ∨ k = 5 ∧ off = 336#64 ∨ k = 6 ∧ off = 604#64 ∨
      k = 7 ∧ off = 652#64 ∨ k = 8 ∧ off = 516#64 ∨ k = 9 ∧ off = 748#64 ∨
      k = 10 ∧ off = 380#64 ∨ k = 11 ∧ off = 700#64)
    (hlen_enc : (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck).length < 2 ^ 63)
    (hcur_lt : (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest).length < 2 ^ 63)
    (hcur_le : (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest).length ≤ x.bs.length)
    (hcur_suf : IsDropSuffix x.bs (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest))
    (hbs_lt56 : x.bs.length < 2 ^ 56)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hFit : FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps))
    (harm : ∀ s' : State,
      V1StateTagEntryHypPlaced H s0 x default (tlb_lenPrefixed (encodeRawK ck) rest)
        .lengthDelimited rest.length s' →
      s'.pc = (blkPl_298).base + off →
      SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s'
        (v1StateLoopPrePlaced A lim st0 s0 s' x.msgPtr x.bufRef x.slot x.ptr default x.bs
          (tlb_lenPrefixed (encodeRawK ck) rest))
        (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_298).base + 216#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 816#64) (htr : s.v1TraceEq s0)
    (hregs : V1StateLoopRegsPlaced s0 x rest.length s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R) := by
  let cur := encodeMessage encodeRawK (BitVec.ofNat 32 k) ck ++ rest
  let rest_k := tlb_lenPrefixed (encodeRawK ck) rest
  let key := BitVec.ofNat 64 (8 * k + 2)
  have hk_or : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
      k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by
    rcases hk_cases with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ |
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))
  obtain ⟨_hlen_ck64, hgt_lim, hd, hk_lt, hwt, htag_k, hk_le, hitag0⟩ :=
    e2m_encodeMessage_split encodeRawK k ck rest hk_or hlen_enc
  rcases hregs with ⟨hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt (Nat.not_le_of_gt hgt_lim) hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hFit_dv : FitsEnv M lim st0 (DecodeVarint2Env cur) := fun evs hevs =>
    e2m_decodeVarint2Env_eq_nil hd hevs ▸
      hFit [] ((SpqrTightEvs.of_freeOnly FreeOnlyEvs.nil).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv ?_
  conv =>
    arg 4
    rw [v1StateLoopPrePlaced, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      v1StateBelow_decodeVarint2 (s0.sp - 816#64)]
    simp only [sepConj_assoc]
  wp_steps_sync_pool (lsmpl.base 291); wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c)
    (x := (⟨x.bufRef, x.slot, curPtr, cur⟩, st0))
    (ret_pc := (blkPl_298).base + 236#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]; simp only [arm64_norm, hsp, hx19])
    (by exact ⟨hcur_lt, hFit_dv⟩)
    (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hx29_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29] at hpcm hrunm hspm hx19_m hx20_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hvregs_m
  have hrest_lt_cur : rest_k.length < cur.length := decodeVarint_length hd
  have hrest_le_cur : rest_k.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
  have hrest_le : rest_k.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
  have hrest_lt : rest_k.length < 2 ^ 63 := Nat.lt_trans hrest_lt_cur hcur_lt
  have hrest_suf : IsDropSuffix x.bs rest_k :=
    suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
  have hshr := key_shr32_of_lt hk_lt
  obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
  obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_lt
  obtain ⟨hw1_zext1, hw1_zext2⟩ :=
    bv32_zeroExtend_ofNat (n := key.toNat / 8) (Nat.lt_of_le_of_lt hk_le (by decide))
  obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_lt hitag0
  have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
    rw [htag_k, beq_eq_false_iff_ne]
    rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 268#64) hinv_m ?_
  conv =>
    arg 4
    simp only [decodeVarint2Spec, decodeVarint2SpecGen, cur, hd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm_eq
  wp_focus_pure; intro hevs_dv
  simp only [arm64_norm] at hsm0 hsm1
  have hevs_nil := e2m_decodeVarint2Env_eq_nil hd hevs_dv
  conv =>
    arg 4
    rw [hevs_nil]
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    simp only [arm64_norm, hsp]
  have htrm : sm.v1TraceEq _ := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
  apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_mono A.repAlloc x.msgPtr (default : V1State).innerState hrest_le_cur) (by sep_focus)
  wp_steps_sync_pool ((blkPl_298).base + 268#64); wp_reach; intro hinv'
  apply SepWPp.weaken_pre
    (P' := v1StateLoopPrePlaced A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs rest_k)
    (Entails.of_eq (by dsimp only [v1StateLoopPrePlaced, AllocCostModel.stepEvents, List.foldl]; sep_ac_rfl))
  exact e2m_jump_arm_placed hsp_align hrest_le hrest_lt hrest_suf
    (by change rest_k.length < 2 ^ 56; exact Nat.lt_of_le_of_lt hrest_le hbs_lt56)
    hk_le htag_k hk_cases harm
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
    (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
    (by simp only [arm64_norm])
    (by simp only [arm64_norm, hsm1])
    (by simp only [arm64_norm]; dsimp only [key] at hw1_zext1; rw [htag_k] at hw1_zext1 ⊢; exact hw1_zext1)
    ⟨by simp only [arm64_norm, hx19_m], by simp only [arm64_norm, hx20_m], by simp only [arm64_norm, hx22_m],
     by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
     by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
     by simp only [arm64_norm, hx29_m]⟩ hinv'

/-- Bundled canonical continuation hypothesis at loop header `+216` (`m = default`, `cur = pb.encodeRaw ++ rest`). -/
def E2mAt216Hyp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat)
    (H : String → Option (State → State)) : Prop :=
  ∀ (x : V1StateMergeGhost) (st0 : M.σ) (R : SepProp) (s0 s : State)
    (pb : V1State) (rest : List (BitVec 8)),
    tlb_V1StateMergeDom x →
    FitsEnv M lim st0 (tlb_V1StateMergeTightEnvOf maxOps) →
    tlb_ValidV1StatePB pb →
    x.bs = tlb_lenPrefixed (V1State.encodeRaw pb) rest →
    x.bs.length < 2 ^ 56 →
    (V1State.encodeRaw pb).length < 2 ^ 63 →
    (V1State.encodeRaw pb).length < 2 ^ 64 →
    (V1State.encodeRaw pb ++ rest).length < 2 ^ 63 →
    (V1State.encodeRaw pb ++ rest).length ≤ x.bs.length →
    IsDropSuffix x.bs (V1State.encodeRaw pb ++ rest) →
    rest.length ≤ x.bs.length →
    IsDropSuffix x.bs rest →
    (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
      some (pb, rest) →
    (s0.sp &&& 15#64 == 0#64) = true →
    s.pc = (blkPl_298).base + 216#64 →
    s.status = .Running → s.sp = s0.sp - 816#64 → s.v1TraceEq s0 →
    V1StateLoopRegsPlaced s0 x rest.length s →
    LibsignalCodeRoLoaded lsmpl s.mem →
    SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s
      (v1StateLoopPrePlaced A lim st0 s0 s x.msgPtr x.bufRef x.slot x.ptr default x.bs
        (V1State.encodeRaw pb ++ rest))
      (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R)

/-- Canonical Block `298` prologue (`+0 → +60 → +216`) under `e2mDomSpec`. -/
theorem e2m_prologue_to_216_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {H : String → Option (State → State)}
    (hVarintCall : subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hAt216 : E2mAt216Hyp A lim maxOps H) :
    subroutine_ok ((blkPC_298).rebase (blkPl_298).base H)
      (blkPl_298).base
      (withLsCodeRoLoaded lsmpl (e2mDomSpec A lim maxOps)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp e2mDomSpec
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  dsimp only at *
  apply SepWPp.elim_lscroProp; intro hinv0
  change SepWPp ((blkPC_298).rebase (blkPl_298).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (e2mDomSpec A lim maxOps) (x, st0) R s0) (WppPanicFalse R)
  have hDom := h.dom
  have hFit0 := h.fit
  obtain ⟨hwt_p, hm_none, pb, rest, hValid, hbs_eq⟩ := hDom
  have hwt_ld : x.wt = .lengthDelimited := e2m_wt_eq_lengthDelimited hwt_p
  have hm_def : x.msg = default := e2m_v1State_eq_default_of_none hm_none
  let raw := V1State.encodeRaw pb
  let rest0 := raw ++ rest
  let len := BitVec.ofNat 64 raw.length
  obtain ⟨hraw_lt63, hraw_lt64, _hrest_lt63, _hrest0_lt_lp⟩ :=
    e2m_lenPrefixed_bounds (hbs_eq ▸ h_4)
  have hdv0 : decodeVarint x.bs = some (len, rest0) :=
    hbs_eq ▸ e2m_decodeVarint_lenPrefixed raw rest
  have hFit_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) := fun evs hevs =>
    e2m_decodeVarint2Env_eq_nil hdv0 hevs ▸
      hFit0 [] ((SpqrTightEvs.of_freeOnly FreeOnlyEvs.nil).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _))
  have hsome_top :
      (mergeMessage V1State.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 100).toOption =
        some (pb, rest) :=
    hbs_eq ▸ e2m_v1State_mergeMessage_canonical hwt_p hm_none hraw_lt64
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0 ?_
  (conv => arg 4; rw [stackAt_v1StateMerge_prologue s0.sp, v1StateBelow_decodeVarint2 (s0.sp - 816#64)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro v0
  apply SepWP.exists_elim; intro v1
  apply SepWP.exists_elim; intro v2
  apply SepWP.exists_elim; intro v3
  apply SepWP.exists_elim; intro v4
  apply SepWP.exists_elim; intro v5
  apply SepWP.exists_elim; intro v6
  apply SepWP.exists_elim; intro v7
  apply SepWP.exists_elim; intro v8
  apply SepWP.exists_elim; intro v9
  apply SepWP.exists_elim; intro v10
  apply SepWP.exists_elim; intro v11
  wp_steps_sync_pool (lsmpl.base 291)
  apply SepWP.fold (v1Proof_savedRegs_intro s0.sp s0) (by sep_focus)
  wp_reach; intro hinv0'
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim) (hinv := hinv0')
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_298).base + 60#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by conv_lhs => dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]; simp only [arm64_norm, h_3])
    (by exact ⟨h_4, hFit_dv0⟩)
    (by sep_focus)
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun _ _ => wppPanicFalse_of_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, _hx21_m, _hx22_m, _hx23_m, _hx24_m, _hx25_m, _hx26_m, _hx27_m, _hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hrunm hspm hx19_m hx20_m hfp_m hvregs_m
  have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_trans hrest0_lt_bs h_4
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hlen_nat : len.toNat = raw.length := by
    dsimp only [len]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_lt64]
  have hlt_len : ¬ rest0.length < len.toNat := by
    rw [hlen_nat]
    dsimp only [rest0, raw]
    rw [List.length_append]
    omega
  have hlim_eq : rest0.length - len.toNat = rest.length := by
    rw [hlen_nat]
    dsimp only [rest0, raw]
    rw [List.length_append]
    omega
  have hrest_le_rest0 : rest.length ≤ rest0.length := by
    dsimp only [rest0, raw]; rw [List.length_append]; omega
  have hrest_le_bs : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_rest0 hrest0_le
  have hrest_suf_rest0 : IsDropSuffix rest0 rest := by
    dsimp only [IsDropSuffix, rest0]
    rw [show (raw ++ rest).length - rest.length = raw.length by rw [List.length_append]; omega]
    exact List.drop_left.symm
  have hrest_suf_bs : IsDropSuffix x.bs rest :=
    suffix_trans hrest0_le hrest0_suf hrest_le_rest0 hrest_suf_rest0
  have hule := ule_len_of_ge hlt_len hrest0_lt
  have hsub := bv_len_sub_limit hlt_len
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_298).base + 216#64) hinvm ?_
  conv =>
    arg 4
    simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm_eq
  wp_focus_pure; intro hevs_dv
  simp only [arm64_norm] at hsm0 hsm1
  have hevs_nil := e2m_decodeVarint2Env_eq_nil hdv0 hevs_dv
  conv =>
    arg 4
    rw [hevs_nil]
    dsimp only [AllocCostModel.stepEvents, List.foldl]
    simp only [arm64_norm]
  have htrm : sm.v1TraceEq s0 := ⟨by simpa only [arm64_norm] using htrm_eq, hvregs_m⟩
  apply SepWP.fold (v1StateBelow_decodeVarint2_entails (s0.sp - 816#64)) (by sep_focus)
  apply SepWP.fold (optProtoInnerStateCapAt_mono A.repAlloc x.msgPtr x.msg.innerState hrest0_le) (by sep_focus)
  conv =>
    arg 4
    rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
    simp only [sepConj_assoc]
  wp_steps_sync_pool ((blkPl_298).base + 216#64)
  wp_reach; intro hinvm'
  apply SepWPp.weaken_pre
    (P' := v1StateLoopPrePlaced A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr default x.bs rest0)
    (Entails.of_eq (by
      dsimp only [v1StateLoopPrePlaced]
      rw [hm_def, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
      sep_ac_rfl))
  exact hAt216 x st0 R s0 _ pb rest h.dom hFit0 hValid hbs_eq
    (optInnerStatePolyBound_lt_2_56 h_5) hraw_lt63 hraw_lt64 hrest0_lt
    hrest0_le hrest0_suf hrest_le_bs hrest_suf_bs hsome_top hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
    (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
    ⟨by simp only [arm64_norm, hx19_m],
     by simp only [arm64_norm, hx20_m],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm],
     by simp only [arm64_norm]; congr 1; dsimp only [rest0, raw]; rw [List.length_append]; omega,
     by simp only [arm64_norm, hfp_m]⟩
    hinvm'

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateMergeTightDefs
