/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetSteps
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Verification of `Chunked.HeaderSent::merge` (Block `302`)

Proves the budget-threaded outer loop induction and top-level contract
`chunked_header_sent_merge_cl_placed_ok_of_contracts` against
`withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)` on Block `302`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix decodeVarint_suffix
   itag_beq_tag_false pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAt suffix_trans
   ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved OptPolyDecoderBound OptPolyEncoderBound
   SepWPpLscro blkPC_302 blkPl_302 bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedHeaderSentMerge_fnOff chunkedHeaderSentPBCapAt_entails_pb
   chunkedHeaderSentPBCapAt_mono chunkedHeaderSent_mergeField_other
   chunkedHeaderSent_mergeField_tag1 chunkedHeaderSent_mergeField_tag2
   chunkedHeaderSent_mergeField_tag3 chunkedInlBelowStack
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlSavedRegs10 codecWireTypeToProto memRegion_48_cells1_160 memRegion_48_wtErr160
   mergeLoopBin mergeLoopBin_of_key_ok mergeMessageBin
   mergeMessageBin_eq_proto_mergeMessage optPolyDecoderBound_mono optPolyDecoderBound_of_merge
   optPolyDecoderPtsLen optPolyEncoderBound_mono optPolyEncoderBound_of_merge
   optPolyEncoderPolysLen optPolyEncoderPtsLen polynomialDecoder_mergeMessage_pts_le
   polynomialEncoder_mergeMessage_pts_polys_le
   protoPrefixStep_chunked_headerSent_mergeField proto_mergeMessage_suffix
   stackAt_chunkedInl_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   withLscroProp wtErr160_entails_memRegion40 wt_beq_two_of_lengthDelimited
   wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeIterEnv SpqrMergeLoopEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv chunkedHeaderSentMergeSpec
   chunkedHeaderSentMergeSpecOfEnv headerSentPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm sepWPpLscro_pure_elim spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
  (chunkedHeaderSent_decode_key_step_cl_placed chunkedHeaderSent_loop_le_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetSteps
  (chunkedHeaderSent_skip_step_cl_placed chunkedHeaderSent_tag1_step_cl_placed
   chunkedHeaderSent_tag2_step_cl_placed chunkedHeaderSent_tag3_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcClPlacedBudget
  (chunkedHeaderSent_from_err_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (chunkedHeaderSentErrFrame chunkedHeaderSentLoopPre chunkedHeaderSent_ret_err_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderSentMerge_fnOff

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem pool_entails_spqrPoolAt_snoc0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) {maxLen polyBound : Nat}
    {evs : List AllocEvent} (h : SpqrMergeIterEnv maxLen polyBound evs) :
    A.pool lim (M.stepEvents evs st) s ⊢ spqrPoolAt A lim st 1 maxLen polyBound s :=
  pool_entails_spqrPoolAt_snoc (evs₁ := []) (evs₂ := evs) A lim st (VmPreserved.refl s)
    (Nat.le_refl 1) (SpqrMergeLoopEnv.nil (fuel := 0)) h

private theorem pool_entails_spqrPoolAt_nil0 {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (f maxLen polyBound : Nat)
    {evs : List AllocEvent} (hnil : evs = []) :
    A.pool lim (M.stepEvents evs st) s ⊢ spqrPoolAt A lim st f maxLen polyBound s :=
  pool_entails_spqrPoolAt_nil (evs₁ := []) (evs₂ := evs) A lim st (VmPreserved.refl s)
    (Nat.zero_le f) (SpqrMergeLoopEnv.nil (fuel := 0)) hnil

private theorem pool_entails_spqrPoolAt_init {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (maxLen polyBound : Nat) :
    A.pool lim st s ⊢ spqrPoolAt A lim st 0 maxLen polyBound s :=
  pool_entails_spqrPoolAt_nil0 A lim st s 0 maxLen polyBound rfl

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

private theorem chunkedHeaderSent_dispatch_step_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)}
    {iwt : WireType} {tag outerLimit : Nat} (htag_lt : tag < 2 ^ 32)
    (htag1 : tag = 1 → ∀ (s1 : State),
      s1.pc = (blkPl_302).base + 344#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s1
        (chunkedHeaderSentLoopPre A lim st s0 s1 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (htag2 : tag = 2 → ∀ (s1 : State),
      s1.pc = (blkPl_302).base + 292#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s1
        (chunkedHeaderSentLoopPre A lim st s0 s1 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (htag3 : tag = 3 → ∀ (s1 : State),
      s1.pc = (blkPl_302).base + 244#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s1
        (chunkedHeaderSentLoopPre A lim st s0 s1 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hother : tag ≠ 1 → tag ≠ 2 → tag ≠ 3 → ∀ (s1 : State),
      s1.pc = (blkPl_302).base + 400#64 →
      s1.status = .Running → s1.sp = s0.sp - 128#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      (s1.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot → s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s1.readReg64 (Reg.gpr 23#5) = 1#64 → s1.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s1.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s1 →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s1
        (chunkedHeaderSentLoopPre A lim st s0 s1 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (headerSentPolyCapBound x))
      (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  by_cases h1 : tag = 1
  · subst h1
    apply sepWPpLscro_of_vm (mid := entry + 344#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
          (headerSentPolyCapBound x))
        (by dsimp only [chunkedHeaderSentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
      exact htag1 rfl _
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
        (by simp only [arm64_norm, wp_norm, hx0]) (by simp only [arm64_norm, wp_norm, hx19])
        (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
        (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx23])
        (by simp only [arm64_norm, wp_norm, hx24]) (by simp only [arm64_norm, wp_norm, hx25])
        ⟨by simp only [arm64_norm, wp_norm, hx27],
         by simp only [arm64_norm, wp_norm, hx28],
         by simp only [arm64_norm, wp_norm, hvregs]⟩
  · by_cases h2 : tag = 2
    · subst h2
      apply sepWPpLscro_of_vm (mid := entry + 292#64)
      by_vm_steps
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
            (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
        exact htag2 rfl _
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
          (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
          (by simp only [arm64_norm, wp_norm, hx0]) (by simp only [arm64_norm, wp_norm, hx19])
          (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
          (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx23])
          (by simp only [arm64_norm, wp_norm, hx24]) (by simp only [arm64_norm, wp_norm, hx25])
          ⟨by simp only [arm64_norm, wp_norm, hx27],
           by simp only [arm64_norm, wp_norm, hx28],
           by simp only [arm64_norm, wp_norm, hvregs]⟩
    · by_cases h3 : tag = 3
      · subst h3
        apply sepWPpLscro_of_vm (mid := entry + 244#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
              (headerSentPolyCapBound x))
            (by dsimp only [chunkedHeaderSentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
          exact htag3 rfl _
            (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
            (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
            (by simp only [arm64_norm, wp_norm, hx0]) (by simp only [arm64_norm, wp_norm, hx19])
            (by simp only [arm64_norm, wp_norm, hx20]) (by simp only [arm64_norm, wp_norm, hx21])
            (by simp only [arm64_norm, wp_norm, hx22]) (by simp only [arm64_norm, wp_norm, hx23])
            (by simp only [arm64_norm, wp_norm, hx24]) (by simp only [arm64_norm, wp_norm, hx25])
            ⟨by simp only [arm64_norm, wp_norm, hx27],
             by simp only [arm64_norm, wp_norm, hx28],
             by simp only [arm64_norm, wp_norm, hvregs]⟩
      · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false h1 htag_lt (by decide : 1 < 2 ^ 32)
        obtain ⟨hb2_1, _⟩ := itag_beq_tag_false h2 htag_lt (by decide : 2 < 2 ^ 32)
        obtain ⟨hb3_1, _⟩ := itag_beq_tag_false h3 htag_lt (by decide : 3 < 2 ^ 32)
        have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) == 1#32) = false := by
          rw [sf_truncate32_ofNat64]; exact hb1_1
        have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) == 2#32) = false := by
          rw [sf_truncate32_ofNat64]; exact hb2_1
        have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) == 3#32) = false := by
          rw [sf_truncate32_ofNat64]; exact hb3_1
        have hb3_bne1 : (BitVec.ofNat 32 tag != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
        have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) != 3#32) = true := by
          simp only [bne, hb3_2, Bool.not_false]
        apply sepWPpLscro_of_vm (mid := entry + 400#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
              (headerSentPolyCapBound x))
            (by dsimp only [chunkedHeaderSentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
          exact hother h1 h2 h3 _
            (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
            (by simp only [arm64_norm, wp_norm, hsp]) (by simp only [arm64_norm, wp_norm, htr])
            (by simp only [arm64_norm, wp_norm, hx0])
            (by simp only [arm64_norm, wp_norm, hx1, sf_truncate32_ofNat64])
            (by simp only [arm64_norm, wp_norm, hx19]) (by simp only [arm64_norm, wp_norm, hx20])
            (by simp only [arm64_norm, wp_norm, hx21]) (by simp only [arm64_norm, wp_norm, hx22])
            (by simp only [arm64_norm, wp_norm, hx23]) (by simp only [arm64_norm, wp_norm, hx24])
            (by simp only [arm64_norm, wp_norm, hx25])
            ⟨by simp only [arm64_norm, wp_norm, hx27],
             by simp only [arm64_norm, wp_norm, hx28],
             by simp only [arm64_norm, wp_norm, hvregs]⟩

theorem chunkedHeaderSent_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
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
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.HeaderSent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptPolyEncoderBound m.sendingEk cur.length →
      OptPolyDecoderBound m.receivingCt1 cur.length →
      Nat.max (m.sendingEk.getD default).pts.length (m.sendingEk.getD default).polys.length +
        cur.length ≤ headerSentPolyCapBound x →
      (m.receivingCt1.getD default).pts.length + cur.length ≤ headerSentPolyCapBound x →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.HeaderSent.mergeField
          (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_302).base + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderSentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _hbound_ek _hbound_ct1 _hcap_ek _hcap_ct1 hres
      hpc hrun hsp htr hx19 hx20 hx21 hx22 _hx23 _hx24 _hx25 hcs
    exact chunkedHeaderSent_loop_le_exit_cl_placed hFromCall hFit (by omega) hsp_align
      hcur_le hcur_suf hlim_lt hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound_ek hbound_ct1 hcap_ek hcap_ct1 hres
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedHeaderSent_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align
        hcur_le hcur_suf hlim_lt hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderSent_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_ek_rest : OptPolyEncoderBound m.sendingEk rest.length :=
        optPolyEncoderBound_mono hbound_ek hrest_le_cur
      have hbound_ct1_rest : OptPolyDecoderBound m.receivingCt1 rest.length :=
        optPolyDecoderBound_mono hbound_ct1 hrest_le_cur
      have hcap_ek_rest : Nat.max (m.sendingEk.getD default).pts.length (m.sendingEk.getD default).polys.length +
          rest.length ≤ headerSentPolyCapBound x := by omega
      have hcap_ct1_rest : (m.receivingCt1.getD default).pts.length + rest.length ≤ headerSentPolyCapBound x := by omega
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_headerSent_mergeField hle_lim hd hk_ge hwt hitag0
      refine chunkedHeaderSent_dispatch_step_placed htag_lt ?_ ?_ ?_ ?_
        hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hcs'
      · intro htag1 s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        rw [htag1, chunkedHeaderSent_mergeField_tag1] at hstep
        refine chunkedHeaderSent_tag1_step_cl_placed hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall
          hFit hsp_align hbs_lt hrest_le hrest_lt hrest_suf
          (fun huc_none => by rw [hres, hstep, huc_none]; rfl)
          (fun uc' rest' s'' huc_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix huc_some).1
        exact ih { m with uc := some uc' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix huc_some).2)
          (optPolyEncoderBound_mono hbound_ek_rest hr'_le)
          (optPolyDecoderBound_mono hbound_ct1_rest hr'_le)
          (by dsimp only; omega)
          (by dsimp only; omega)
          (by rw [hres, hstep, huc_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · intro htag2 s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        rw [htag2, chunkedHeaderSent_mergeField_tag2] at hstep
        refine chunkedHeaderSent_tag2_step_cl_placed hPushCall hPolyEncCall
          hFit hsp_align hrest_le hrest_suf hbound_ek_rest hcap_ek_rest
          (fun hpoly_none => by rw [hres, hstep, hpoly_none]; rfl)
          (fun d' rest' s'' hpoly_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_some).1
        obtain ⟨hpts_le, hpolys_le⟩ := polynomialEncoder_mergeMessage_pts_polys_le hpoly_some
        exact ih { m with sendingEk := some d' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hpoly_some).2)
          (optPolyEncoderBound_of_merge hbound_ek_rest hpoly_some)
          (optPolyDecoderBound_mono hbound_ct1_rest hr'_le)
          (by dsimp only [Option.getD_some]; simp only [Nat.max_def] at hcap_ek_rest ⊢; split <;> split at hcap_ek_rest <;> omega)
          (by dsimp only; omega)
          (by rw [hres, hstep, hpoly_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · intro htag3 s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        rw [htag3, chunkedHeaderSent_mergeField_tag3] at hstep
        refine chunkedHeaderSent_tag3_step_cl_placed hPushCall hPolyDecCall
          hFit hsp_align hrest_le hrest_suf hbound_ct1_rest hcap_ct1_rest
          (fun hpoly_none => by rw [hres, hstep, hpoly_none]; rfl)
          (fun d' rest' s'' hpoly_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_some).1
        have hpts_le := polynomialDecoder_mergeMessage_pts_le hpoly_some
        exact ih { m with receivingCt1 := some d' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hpoly_some).2)
          (optPolyEncoderBound_mono hbound_ek_rest hr'_le)
          (optPolyDecoderBound_of_merge hbound_ct1_rest hpoly_some)
          (by dsimp only; omega)
          (by dsimp only [Option.getD_some]; omega)
          (by rw [hres, hstep, hpoly_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · intro hne1 hne2 hne3 s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        rw [chunkedHeaderSent_mergeField_other m iwt rest 98 htag_lt hne1 hne2 hne3] at hstep
        refine chunkedHeaderSent_skip_step_cl_placed hSkipCall hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt
          (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl)
          (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
        have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
        exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some))
          (optPolyEncoderBound_mono hbound_ek_rest hr'_le)
          (optPolyDecoderBound_mono hbound_ct1_rest hr'_le)
          (by omega)
          (by omega)
          (by rw [hres, hstep, hsf_some]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''

theorem chunked_header_sent_merge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
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
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim))) :
    subroutine_ok ((blkPC_302).rebase (blkPl_302).base H)
      (blkPl_302).base
      (withLsCodeRoLoaded lsmpl (chunkedHeaderSentMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedHeaderSentMergeSpec chunkedHeaderSentMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbound_ek, hbound_ct1, hFit⟩
  have hbs_lt : x.bs.length < 2 ^ 63 := by unfold OptPolyDecoderBound at hbound_ct1; omega
  have hret_err := @chunkedHeaderSent_ret_err_exit_placed _ M A lim H x st R s0 x.msg
  have hfrom_err := @chunkedHeaderSent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedHeaderSent_loop_ok_cl_placed _ M A lim H
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall hPolyEncCall hPolyDecCall
      x st R s0 outerLimit hFit hsp_align hbs_lt hlim_lt
  have hsaved :
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
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
          by simpa only [AllocCostModel.stepEvents, List.foldl] using
               fitsEnv_decodeVarint2_of_spqr (f₀ := 0) (by omega) SpqrMergeLoopEnv.nil hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
        at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint x.bs with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_headerSent_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 124#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc0 A lim st sm
              (polyBound := headerSentPolyCapBound x) (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              memRegion (s0.sp - 128#64) 48 ∗
              chunkedHeaderSentErrFrame A lim st 1 (headerSentPolyCapBound x)
                s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      | some p =>
        rcases p with ⟨len, rest0⟩
        have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
        have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
        have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
        have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
        let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
        by_cases hlt_len : rest0.length < len.toNat
        · have hule := ule_len_of_lt hlt_len hrest0_lt
          have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_headerSent_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 112#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, memRegion_48_cells1_160 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm 0 x.bs.length
                (headerSentPolyCapBound x) (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗
                memRegion (s0.sp - 120#64) 40 ∗
                stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                chunkedHeaderSentErrFrame A lim st 0 (headerSentPolyCapBound x)
                  s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
              (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
            exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hpts_ek_init : (x.msg.sendingEk.getD default).pts.length = optPolyEncoderPtsLen x.msg.sendingEk := by
            (cases x.msg.sendingEk <;> simp [optPolyEncoderPtsLen]); rfl
          have hpolys_ek_init : (x.msg.sendingEk.getD default).polys.length = optPolyEncoderPolysLen x.msg.sendingEk := by
            (cases x.msg.sendingEk <;> simp [optPolyEncoderPolysLen]); rfl
          have hpts_ct1_init : (x.msg.receivingCt1.getD default).pts.length = optPolyDecoderPtsLen x.msg.receivingCt1 := by
            (cases x.msg.receivingCt1 <;> simp [optPolyDecoderPtsLen]); rfl
          have hcap_ek0 : Nat.max (x.msg.sendingEk.getD default).pts.length (x.msg.sendingEk.getD default).polys.length +
              rest0.length ≤ headerSentPolyCapBound x := by
            unfold headerSentPolyCapBound; rw [hpts_ek_init, hpolys_ek_init]
            simp only [Nat.max_def]; repeat (split <;> try omega)
          have hcap_ct10 : (x.msg.receivingCt1.getD default).pts.length + rest0.length ≤ headerSentPolyCapBound x := by
            unfold headerSentPolyCapBound; rw [hpts_ct1_init]
            simp only [Nat.max_def]; repeat (split <;> try omega)
          have hres0 : (mergeMessage V1State.Chunked.HeaderSent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.HeaderSent.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_headerSent_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
                conv_rhs => rw [hrest0_suf, List.drop_drop]
                congr 1; omega
              simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                hdv0_p, Except.toOption, hlt_len, hdrop_eq]
              rcases mergeLoopBin V1State.Chunked.HeaderSent.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 168#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedHeaderSentPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm (6 * (x.bs.length - rest0.length))
                x.bs.length (headerSentPolyCapBound x)
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                x.msg x.bs rest0 (headerSentPolyCapBound x))
              (by dsimp only [chunkedHeaderSentLoopPre, sliceCursorAfter]; sep_entail)
            exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf
              (optPolyEncoderBound_mono hbound_ek hrest0_le)
              (optPolyDecoderBound_mono hbound_ct1 hrest0_le)
              hcap_ek0 hcap_ct10 hres0
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
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_headerSent_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply sepWPpLscro_of_vm (mid := entry + 112#64)
    by_vm_steps
      (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
      apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
      apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
      apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
      apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
      apply SepWP.fold
        (pool_entails_spqrPoolAt_init A lim st s0 x.bs.length (headerSentPolyCapBound x))
        (by sep_focus)
      wp_steps
      apply SepWP.fold hsaved (by sep_focus)
      apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
      apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedHeaderSentErrFrame A lim st 0 (headerSentPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
      exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm]⟩

alias chunked_header_sent_merge_placed_ok_of_contracts :=
  chunked_header_sent_merge_cl_placed_ok_of_contracts

alias chunkedHeaderSent_merge_placed_ok_of_contracts :=
  chunked_header_sent_merge_cl_placed_ok_of_contracts

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudget
