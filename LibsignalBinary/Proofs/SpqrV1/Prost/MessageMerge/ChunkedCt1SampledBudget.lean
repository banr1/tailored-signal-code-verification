/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps
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
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# SPQR V1: Budget-Threaded Loop & Top-Level Proof for `Chunked.Ct1Sampled::merge` (Block `300`)

Proves the budget-threaded `[LibsignalPlacement]` loop invariant and top-level contract
`chunked_ct1_sampled_merge_cl_placed_ok_of_contracts` for
`prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::Ct1Sampled, &mut &[u8]>`
(Block `300`) against `withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix decodeVarint_suffix itag_beq_tag_false
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
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
  (ChunkedCt1SampledMergeGhost ChunkedLoopRegs SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedBelow
   chunkedBelow_leaf chunkedBelow_leaf_entails
   chunkedCt1SampledMerge_fnOff
   chunkedCt1SampledPBCapAt_entails_pb chunkedCt1SampledPBCapAt_mono
   chunkedCt1Sampled_mergeField_other chunkedCt1Sampled_mergeField_tag1
   chunkedCt1Sampled_mergeField_tag2 chunkedCt1Sampled_mergeField_tag3
   chunkedSavedRegs codecWireTypeToProto
   memRegion_48_split_128 memRegion_48_wtErr128 mergeLoopBin
   mergeLoopBin_of_key_ok mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   optPolyDecoderPtsLen optPolyDecoder_getD_default_pts_len
   optPolyEncoderPolysLen optPolyEncoderPtsLen
   optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
   polyDecoder_mergeMessage_pts_len polyEncoder_mergeMessage_pts_polys_len
   protoPrefixStep_chunked_ct1Sampled_mergeField proto_mergeMessage_suffix
   stackAt_chunkedMerge subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   withLscroProp wtErr128_entails_memRegion40 wt_beq_two_of_lengthDelimited
   wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_300 blkPl_300)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (ct1SampledErrFrame ct1SampledLoopPre
   ct1Sampled_decode_key_step_cl_placed ct1Sampled_err0_ret_exit_placed
   ct1Sampled_from_err_exit_cl_placed ct1Sampled_loop_le_exit_cl_placed
   stackAt_decodeVarint2_raw_eq)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps
  (ct1Sampled_skip_step_cl_placed ct1Sampled_tag1_step_cl_placed
   ct1Sampled_tag2_step_cl_placed ct1Sampled_tag3_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1SampledMergeEnv SpqrMergeIterEnv SpqrMergeLoopEnv
   chunkedCt1SampledMergeSpec chunkedCt1SampledMergeSpecOfEnv
   ct1SampledPolyCapBound decodeErrorPushMergeBudgetSpec
   unchunkedCt1SentMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm sepWPpLscro_pure_elim spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedCt1SampledMerge_fnOff

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
local notation "entry" => (blkPl_300).base

theorem ct1Sampled_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.Ct1Sampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      optPolyEncoderPtsLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyEncoderPolysLen m.sendingCt1 + cur.length < 2 ^ 56 →
      optPolyDecoderPtsLen m.receivingEk + cur.length < 2 ^ 56 →
      Nat.max (optPolyEncoderPtsLen m.sendingCt1) (optPolyEncoderPolysLen m.sendingCt1) +
        cur.length ≤ ct1SampledPolyCapBound x →
      optPolyDecoderPtsLen m.receivingEk + cur.length ≤ ct1SampledPolyCapBound x →
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
          (cur.length - limit) m cur limit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_300).base + 192#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
        (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur
          (ct1SampledPolyCapBound x))
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have htag1_step := fun {s m rest iwt} =>
    @ct1Sampled_tag1_step_cl_placed _ M A lim H hUcCall hPushCall x st R s0 s m rest iwt limit hFit
  have htag2_step := fun {s m rest iwt} =>
    @ct1Sampled_tag2_step_cl_placed _ M A lim H hPolyEncCall hPushCall x st R s0 s m rest iwt limit hFit
  have htag3_step := fun {s m rest iwt} =>
    @ct1Sampled_tag3_step_cl_placed _ M A lim H hPolyDecCall hPushCall x st R s0 s m rest iwt limit hFit
  have hskip_step := fun {s m rest tag iwt} =>
    @ct1Sampled_skip_step_cl_placed _ M A lim H hSkipCall x st R s0 s m rest iwt tag limit hFit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ _ _ _ _ hres_cur hpc hrun hsp htr _ _ hx21 hx22 hcs
    exact ct1Sampled_loop_le_exit_cl_placed hFromCall hFit (by omega) hsp_align hcur_le hcur_suf
      hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hpts hpolys hdec_pts henc_cap hdec_cap
      hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
    by_cases hle_lim : cur.length ≤ limit
    · exact ct1Sampled_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align hcur_le hcur_suf
        hlim_lt hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ct1Sampled_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_ct1Sampled_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [chunkedCt1Sampled_mergeField_tag1] at hloop_ok
        have hnone_uc :
            (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
              (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
            (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          intro huc; simp only [hres_cur, hloop_ok, huc, Option.map_none]
        apply sepWPpLscro_of_vm (mid := entry + 368#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
              (ct1SampledPolyCapBound x))
            (by dsimp only [ct1SampledLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
          refine htag1_step hsp_align hrest_le hrest_lt hrest_suf hnone_uc
            (fun u' rest' s'' huc hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
            (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
            (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
            (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
            (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
            (by simp only [arm64_norm, wp_norm, hx22'])
            ⟨by simp only [arm64_norm, wp_norm, hx23'], by simp only [arm64_norm, wp_norm, hx24'],
             by simp only [arm64_norm, wp_norm, hx25'],
             ⟨by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
              by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
          have huf := proto_mergeMessage_suffix huc
          have hres_next :
              (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                (rest'.length - limit) { m with uc := some u' } rest' limit 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, huc, Option.map_some]
          exact ih { m with uc := some u' } rest' s''
            (by have := huf.1; omega) (by have := huf.1; omega)
            (suffix_trans hrest_le hrest_suf huf.1 huf.2)
            (by dsimp only; have := huf.1; omega)
            (by dsimp only; have := huf.1; omega)
            (by dsimp only; have := huf.1; omega)
            (by dsimp only; have := huf.1; omega)
            (by dsimp only; have := huf.1; omega)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [chunkedCt1Sampled_mergeField_tag2] at hloop_ok
          have hnone_pe :
              (mergeMessage PolynomialEncoder.mergeField
                (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
              (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            intro hpe; simp only [hres_cur, hloop_ok, hpe, Option.map_none]
          apply sepWPpLscro_of_vm (mid := entry + 316#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
            apply SepWPpLscro.weaken_pre
              (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                (ct1SampledPolyCapBound x))
              (by dsimp only [ct1SampledLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
            refine htag2_step hsp_align hrest_le hrest_suf (by omega) (by omega) (by omega) hnone_pe
              (fun pe' rest' s'' hpe hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22'])
              ⟨by simp only [arm64_norm, wp_norm, hx23'], by simp only [arm64_norm, wp_norm, hx24'],
               by simp only [arm64_norm, wp_norm, hx25'],
               ⟨by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
            have hpf := proto_mergeMessage_suffix hpe
            obtain ⟨hpts_le, hpolys_le⟩ := polyEncoder_mergeMessage_pts_polys_len hpe
            have hpts_eq : (m.sendingCt1.getD default).pts.length = optPolyEncoderPtsLen m.sendingCt1 :=
              optPolyEncoder_getD_default_pts_len m.sendingCt1
            have hpolys_eq : (m.sendingCt1.getD default).polys.length = optPolyEncoderPolysLen m.sendingCt1 :=
              optPolyEncoder_getD_default_polys_len m.sendingCt1
            have hres_next :
                (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                  (rest'.length - limit) { m with sendingCt1 := some pe' } rest' limit 98).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hpe, Option.map_some]
            exact ih { m with sendingCt1 := some pe' } rest' s''
              (by have := hpf.1; omega) (by have := hpf.1; omega)
              (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
              (by dsimp only [optPolyEncoderPtsLen]; omega)
              (by dsimp only [optPolyEncoderPolysLen]; omega)
              (by dsimp only; have := hpf.1; omega)
              (by dsimp only [optPolyEncoderPtsLen, optPolyEncoderPolysLen]
                  have hmax_eq : ∀ a b : Nat, Nat.max a b = max a b := fun _ _ => rfl
                  simp only [hmax_eq] at henc_cap ⊢
                  omega)
              (by dsimp only; have := hpf.1; omega)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb2_1
            rw [htag3] at hx1' hloop_ok
            rw [chunkedCt1Sampled_mergeField_tag3] at hloop_ok
            have hnone_pd :
                (mergeMessage PolynomialDecoder.mergeField
                  (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
                (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hpd; simp only [hres_cur, hloop_ok, hpd, Option.map_none]
            apply sepWPpLscro_of_vm (mid := entry + 268#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
              apply SepWPpLscro.weaken_pre
                (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                  (ct1SampledPolyCapBound x))
                (by dsimp only [ct1SampledLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
              refine htag3_step hsp_align hrest_le hrest_suf (by omega) (by omega) hnone_pd
                (fun pd' rest' s'' hpd hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
                (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
                (by simp only [arm64_norm, wp_norm, hx22'])
                ⟨by simp only [arm64_norm, wp_norm, hx23'], by simp only [arm64_norm, wp_norm, hx24'],
                 by simp only [arm64_norm, wp_norm, hx25'],
                 ⟨by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                  by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
              have hpf := proto_mergeMessage_suffix hpd
              have hdec_le := polyDecoder_mergeMessage_pts_len hpd
              have hdec_eq : (m.receivingEk.getD default).pts.length = optPolyDecoderPtsLen m.receivingEk :=
                optPolyDecoder_getD_default_pts_len m.receivingEk
              have hres_next :
                  (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                    (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                  (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                    (rest'.length - limit) { m with receivingEk := some pd' } rest' limit 98).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hpd, Option.map_some]
              exact ih { m with receivingEk := some pd' } rest' s''
                (by have := hpf.1; omega) (by have := hpf.1; omega)
                (suffix_trans hrest_le hrest_suf hpf.1 hpf.2)
                (by dsimp only; have := hpf.1; omega)
                (by dsimp only; have := hpf.1; omega)
                (by dsimp only [optPolyDecoderPtsLen]; omega)
                (by dsimp only; have := hpf.1; omega)
                (by dsimp only [optPolyDecoderPtsLen]; omega)
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''
          · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
            obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by
              rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by
              simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by
              simp only [bne, hb3_2, Bool.not_false]
            rw [chunkedCt1Sampled_mergeField_other m iwt rest 98 hitag_lt htag1 htag2 htag3] at hloop_ok
            have hnone_sf :
                skipField (2 * rest.length + 2) 98 (key.toNat / 8) iwt rest = none →
                (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            apply sepWPpLscro_of_vm (mid := entry + 172#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
              apply SepWPpLscro.weaken_pre
                (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
                  (ct1SampledPolyCapBound x))
                (by dsimp only [ct1SampledLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm1]; exact Entails.refl _)
              refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0'])
                (by simp only [arm64_norm, wp_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
                (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
                ⟨by simp only [arm64_norm, wp_norm, hx23'], by simp only [arm64_norm, wp_norm, hx24'],
                 by simp only [arm64_norm, wp_norm, hx25'],
                 ⟨by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                  by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩⟩
              have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hres_next :
                  (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
                    (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
                  (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                    (rest'.length - limit) m rest' limit 98).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                rw [hres_cur, hloop_ok, hsf]; rfl
              exact ih m rest' s''
                (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                (by omega) (by omega) (by omega) (by omega) (by omega)
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs''

theorem chunked_ct1_sampled_merge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim))) :
    subroutine_ok ((blkPC_300).rebase (blkPl_300).base H)
      (blkPl_300).base
      (withLsCodeRoLoaded lsmpl (chunkedCt1SampledMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedCt1SampledMergeSpec chunkedCt1SampledMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨hx0_wt, hx1_msg, hx2_buf, hpts_0, hpolys_0, hdec_0, hFit⟩
  have hbs_lt : x.bs.length < 2 ^ 63 := by omega
  have herr0_exit := @ct1Sampled_err0_ret_exit_placed _ M A lim H x st R s0 x.msg
  have hloop := fun (limit : Nat) (hlim_lt : limit < 2 ^ 63) =>
    @ct1Sampled_loop_ok_cl_placed _ M A lim H
      hFromCall hPushCall hVarintCall hSkipCall hUcCall hPolyEncCall hPolyDecCall
      x st R s0 limit hFit hsp_align hbs_lt hlim_lt
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
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [hx0_wt, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
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
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx2_buf],
          hbs_lt,
          by simpa only [AllocCostModel.stepEvents, List.foldl] using
               fitsEnv_decodeVarint2_of_spqr (f₀ := 0) (by omega) SpqrMergeLoopEnv.nil hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hx1_msg, hx2_buf]
        at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint x.bs with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 124#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc0 A lim st sm
              (polyBound := ct1SampledPolyCapBound x) (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
              ct1SampledErrFrame A lim st 1 (ct1SampledPolyCapBound x)
                s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
            (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; sep_ac_rfl))
          exact herr0_exit hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
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
          have hnone : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, memRegion_48_split_128 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm 0 x.bs.length
                (ct1SampledPolyCapBound x) (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 120#64) 40 ∗
                chunkedBelow s0.sp ∗
                ct1SampledErrFrame A lim st 0 (ct1SampledPolyCapBound x)
                  s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
              (Entails.of_eq (by dsimp only [ct1SampledErrFrame]; sep_ac_rfl))
            refine ct1Sampled_from_err_exit_cl_placed (m := x.msg)
              (w := 0x8000000000000007#64) (v_stk0 := v_stk0) (f := 0)
              hFromCall hFit hnone (by omega)
              (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              (by simp only [arm64_norm, wp_norm])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hmax_eq : ∀ a b : Nat, Nat.max a b = max a b := fun _ _ => rfl
          have henc_cap0 : Nat.max (optPolyEncoderPtsLen x.msg.sendingCt1)
              (optPolyEncoderPolysLen x.msg.sendingCt1) + rest0.length ≤ ct1SampledPolyCapBound x := by
            unfold ct1SampledPolyCapBound
            simp only [hmax_eq]
            omega
          have hdec_cap0 : optPolyDecoderPtsLen x.msg.receivingEk + rest0.length ≤
              ct1SampledPolyCapBound x := by
            unfold ct1SampledPolyCapBound
            simp only [hmax_eq]
            omega
          have hres0 : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
              have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
                conv_rhs => rw [hrest0_suf, List.drop_drop]
                congr 1; omega
              simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                hdv0_p, Except.toOption, hlt_len, hdrop_eq]
              rcases mergeLoopBin V1State.Chunked.Ct1Sampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 192#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm (6 * (x.bs.length - rest0.length))
                x.bs.length (ct1SampledPolyCapBound x)
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                x.msg x.bs rest0 (ct1SampledPolyCapBound x))
              (Entails.of_eq (by
                dsimp only [ct1SampledLoopPre]
                rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
                sep_ac_rfl))
            exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf
              (by omega) (by omega) (by omega) henc_cap0 hdec_cap0 hres0
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hsm1, hsub])
              ⟨by simp only [arm64_norm, wp_norm],
               by simp only [arm64_norm, wp_norm],
               by simp only [arm64_norm, wp_norm],
               ⟨by simp only [arm64_norm, wp_norm, hx26_m],
                by simp only [arm64_norm, wp_norm, hx27_m],
                by simp only [arm64_norm, wp_norm, hx28_m],
                by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited hx0_wt hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, hx0_wt]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]
      exact hbne1
    have hnone : (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ct1Sampled_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply sepWPpLscro_of_vm (mid := entry + 108#64)
    by_vm_steps
      (conv => arg 4; rw [stackAt_chunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr128 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
      apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
      apply SepWP.exists_elim; intro v23; apply SepWP.exists_elim; intro v24
      apply SepWP.exists_elim; intro v25; apply SepWP.exists_elim; intro v_lr
      apply SepWP.exists_elim; intro v_fp; apply SepWP.exists_elim; intro b_wt1
      apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
      apply SepWP.fold
        (pool_entails_spqrPoolAt_init A lim st s0 x.bs.length (ct1SampledPolyCapBound x))
        (by sep_focus)
      wp_steps
      apply SepWP.fold hsaved (by sep_focus)
      apply SepWP.fold (wtErr128_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
      apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ v_wt0) ∗ memRegion (s0.sp - 120#64) 40 ∗
          chunkedBelow s0.sp ∗
          ct1SampledErrFrame A lim st 0 (ct1SampledPolyCapBound x)
            s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [ct1SampledErrFrame]; sep_entail)
      refine ct1Sampled_from_err_exit_cl_placed (x := x) (st := st) (R := R) (s0 := s0)
        (m := x.msg) (w := 0x8000000000000006#64) (v_stk0 := v_wt0) (f := 0)
        hFromCall hFit hnone (by omega)
        (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        ?_ ?_ ?_ ?_ ?_ ⟨?_, ?_, ?_, ?_⟩
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm, hrun]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]
      · simp only [arm64_norm, wp_norm]

alias chunked_ct1_sampled_merge_placed_ok_of_contracts :=
  chunked_ct1_sampled_merge_cl_placed_ok_of_contracts

alias chunkedCt1Sampled_merge_cl_placed_ok_of_contracts :=
  chunked_ct1_sampled_merge_cl_placed_ok_of_contracts

alias chunkedCt1Sampled_merge_placed_ok_of_contracts :=
  chunked_ct1_sampled_merge_cl_placed_ok_of_contracts

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudget
