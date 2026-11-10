/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudgetAux
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Auth.Merge
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Budget Verification of `Unchunked.Ct1Sent::merge` (Block `312`)

Proves the loop induction and top-level budget contracts
(`unchunkedCt1SentMerge_own_cl_placed_ok_of_contracts`,
`unchunkedCt1SentMerge_cl_placed_ok_of_contracts`) against
`withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)` on Block `312`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement lsmpl blkPC_312 blkPl_312)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost IsDropSuffix
   decodeVarint_suffix itag_beq_tag_false
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAt suffix_trans
   ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge
  (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1
  (ProtoAuthenticator V1State)
open CryptoVerification.LibsignalSpqrV1.Proto
  (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (HighCalleeSaved24 SepWPpLscro
   bv64_add_zero_u bv64_sub_zero_u bv_len_sub_limit
   codecWireTypeToProto
   memRegion_48_split_112 memRegion_48_wtErr112
   mergeBytes_length mergeBytes_suffix
   mergeLoopBin mergeLoopBin_of_key_ok mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   protoPrefixStep_unchunked_ct1Sent_mergeField
   protoUnchunkedCt1SentCapAt_mono proto_mergeMessage_suffix
   stackAt_unchunkedMerge subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   tag_gt_two_branch
   unchunkedCt1Sent_mergeField_other unchunkedCt1Sent_mergeField_tag1
   unchunkedCt1Sent_mergeField_tag2 unchunkedCt1Sent_mergeField_tag3
   unchunkedCt1Sent_mergeField_tag4 unchunkedCt1Sent_mergeField_tag5
   unchunkedMergeBelow unchunkedMergeBelow_leaf unchunkedMergeBelow_leaf_entails
   withLscroProp wtErr112_entails_memRegion40
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3RawSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeLoopEnv UnchunkedCt1SentMergeEnv decodeErrorPushMergeBudgetSpec
   unchunkedCt1SentMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro
   decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm sepWPpLscro_pure_elim
   spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedBaseBudget
  (subroutine_ok_unchunkedCt1SentMerge_of_own_placed
   unchunkedCt1SentMergeOwnSpec unchunkedCt1SentMergeOwnSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepBudgetAux
  (ct1SentErrFrame ct1SentLoopPre ct1Sent_err0_ret_exit_placed
   protoUnchunkedCt1SentCapAt_entails_any stackAt_decodeVarint2_raw_eq
   unchunkedSavedRegs)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentStepClPlacedBudget
  (ct1Sent_from_err_exit_cl_placed ct1Sent_skip_step_cl_placed
   ct1Sent_tag1_varint_step_cl_placed ct1Sent_tag1_wt_err_step_cl_placed
   ct1Sent_tag2_step_cl_placed ct1Sent_tag3_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudgetAux
  (ct1Sent_decode_key_step_cl_placed ct1Sent_loop_le_exit_cl_placed
   ct1Sent_tag4_step_cl_placed ct1Sent_tag5_step_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
  (skipField3Spec)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudgetAux
  (ct1Sent_tag4_step_cl_placed ct1Sent_tag5_step_cl_placed
   ct1Sent_loop_le_exit_cl_placed ct1Sent_decode_key_step_cl_placed)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_312).base

theorem ct1Sent_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : UnchunkedCt1SentMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit : FitsEnv M lim st (UnchunkedCt1SentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Unchunked.Ct1Sent) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_312).base + 152#64 →
      s.status = .Running → s.sp = s0.sp - 112#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s →
      SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s
        (ct1SentLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0)
        (WppPanicFalse R) := by
  have htag1_varint := fun {s m rest} =>
    @ct1Sent_tag1_varint_step_cl_placed _ M A lim H hPushCall hVarintCall x st R s0 s m rest limit hFit
  have htag1_wt_err := fun {s m rest iwt} =>
    @ct1Sent_tag1_wt_err_step_cl_placed _ M A lim H hFromCall hPushCall x st R s0 s m rest iwt hFit
  have htag2_step := fun {s m rest iwt} =>
    @ct1Sent_tag2_step_cl_placed _ M A lim H hPushCall hAuthCall x st R s0 s m rest iwt limit hFit
  have htag3_step := fun {s m rest iwt} =>
    @ct1Sent_tag3_step_cl_placed _ M A lim H hPushCall hBytesCall x st R s0 s m rest iwt limit hFit
  have htag4_step := fun {s m rest iwt} =>
    @ct1Sent_tag4_step_cl_placed _ M A lim H hPushCall hBytesCall x st R s0 s m rest iwt limit hFit
  have htag5_step := fun {s m rest iwt} =>
    @ct1Sent_tag5_step_cl_placed _ M A lim H hPushCall hBytesCall x st R s0 s m rest iwt limit hFit
  have hskip_step := fun {s m rest iwt tag} =>
    @ct1Sent_skip_step_cl_placed _ M A lim H hSkipCall x st R s0 s m rest iwt tag limit hFit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr _hx19 _hx20 hx21 hx22 _hx23 hcs
    exact ct1Sent_loop_le_exit_cl_placed hFromCall hFit (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
    by_cases hle_lim : cur.length ≤ limit
    · exact ct1Sent_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine ct1Sent_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hcs'
      obtain ⟨hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_unchunked_ct1Sent_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [unchunkedCt1Sent_mergeField_tag1] at hloop_ok
        apply sepWPpLscro_of_vm (mid := entry + 372#64)
        by_vm_steps
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
          apply SepWPpLscro.weaken_pre
            (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
          by_cases hiwt : iwt = .varint
          · subst hiwt
            have hnone_dv : decodeVarint rest = none →
                (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
            refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf hnone_dv
              (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
              (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
              (by simp only [arm64_norm, wp_norm, hx23'])
              ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
               by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
            have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
            have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
            have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) { m with epoch := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
            exact ih { m with epoch := v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''
          · have hnone_wt : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
            exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf hnone_wt
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
               by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [unchunkedCt1Sent_mergeField_tag2] at hloop_ok
          apply sepWPpLscro_of_vm (mid := entry + 276#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            apply SepWPpLscro.weaken_pre
              (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
            have hnone_am : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
                (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro ham; simp only [hres_cur, hloop_ok, ham, Option.map_none]
            refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_am
              (fun v rest' s'' ham hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
              ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
               by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
               by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
            have ⟨hrest'_le_rest, hrest'_suf⟩ := proto_mergeMessage_suffix ham
            have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) { m with auth := some v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, ham, Option.map_some]
            exact ih { m with auth := some v } rest' s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest hrest'_suf)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [unchunkedCt1Sent_mergeField_tag3] at hloop_ok
            apply sepWPpLscro_of_vm (mid := entry + 324#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
              apply SepWPpLscro.weaken_pre
                (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
                (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
              have hnone_mb : mergeBytes iwt rest = none →
                  (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
              refine htag3_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
                (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
                (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
                (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
                ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
                 by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                 by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
              have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
              have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                  (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                  (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) { m with hdr := v } rest' limit 97).map
                    (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                simp only [hres_cur, hloop_ok, hmb, Option.map_some]
              exact ih { m with hdr := v } rest' s'' (by omega) (by omega)
                (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
                hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hloop_ok; rw [unchunkedCt1Sent_mergeField_tag4] at hloop_ok
              apply sepWPpLscro_of_vm (mid := entry + 348#64)
              by_vm_steps
                wp_steps
                apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
                apply SepWPpLscro.weaken_pre
                  (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
                  (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
                have hnone_mb : mergeBytes iwt rest = none →
                    (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                  intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
                refine htag4_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
                  (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
                  (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                  (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                  (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
                  (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
                  (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
                  ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
                   by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                   by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
                have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
                have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                    (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                    (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) { m with es := v } rest' limit 97).map
                      (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                  simp only [hres_cur, hloop_ok, hmb, Option.map_some]
                exact ih { m with es := v } rest' s'' (by omega) (by omega)
                  (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
                  hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''
            · by_cases htag5 : key.toNat / 8 = 5
              · rw [htag5] at hx1' hloop_ok; rw [unchunkedCt1Sent_mergeField_tag5] at hloop_ok
                apply sepWPpLscro_of_vm (mid := entry + 236#64)
                by_vm_steps
                  wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                  refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
                  apply SepWPpLscro.weaken_pre
                    (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
                    (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
                  have hnone_mb : mergeBytes iwt rest = none →
                      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                    intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
                  refine htag5_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
                    (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
                    (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                    (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                    (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
                    (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
                    (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
                    ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
                     by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                     by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
                  have hrest'_le_rest : rest'.length ≤ rest.length := mergeBytes_length hmb
                  have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                      (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) { m with ct1 := v } rest' limit 97).map
                        (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                    simp only [hres_cur, hloop_ok, hmb, Option.map_some]
                  exact ih { m with ct1 := v } rest' s'' (by omega) (by omega)
                    (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
                    hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''
              · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
                have hitag_lt29 : key.toNat / 8 < 2 ^ 29 := by omega
                obtain ⟨hgt2_1, hgt2_2, hgt2_3, hgt2_4⟩ := tag_gt_two_branch (by omega : 2 < key.toNat / 8) hitag_lt29
                obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 hitag_lt (by decide : 3 < 2 ^ 32)
                obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 hitag_lt (by decide : 4 < 2 ^ 32)
                obtain ⟨hb5_1, _⟩ := itag_beq_tag_false htag5 hitag_lt (by decide : 5 < 2 ^ 32)
                have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
                have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
                have hb5_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 5#32) = false := by rw [sf_truncate32_ofNat64]; exact hb5_1
                have hb5_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 5#32) = true := by simp only [bne, hb5_1, Bool.not_false]
                have hb5_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 5#32) = true := by simp only [bne, hb5_2, Bool.not_false]
                rw [unchunkedCt1Sent_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3 htag4 htag5] at hloop_ok
                apply sepWPpLscro_of_vm (mid := entry + 404#64)
                by_vm_steps
                  wp_steps
                  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
                  refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
                  apply SepWPpLscro.weaken_pre
                    (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
                    (by dsimp only [ct1SentLoopPre]; rw [spqrPoolAt_of_vmPreserved hvm_d]; exact Entails.refl _)
                  have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
                    intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
                  refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
                    (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs'' => ?_)
                    (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                    (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                    (by simp only [arm64_norm, wp_norm, hx0'])
                    (by simp only [arm64_norm, wp_norm, hx1', sf_truncate32_ofNat64])
                    (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
                    (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
                    (by simp only [arm64_norm, wp_norm, hx23'])
                    ⟨by simp only [arm64_norm, wp_norm, hx24'], by simp only [arm64_norm, wp_norm, hx25'],
                     by simp only [arm64_norm, wp_norm, hx26'], by simp only [arm64_norm, wp_norm, hx27'],
                     by simp only [arm64_norm, wp_norm, hx28'], by simp only [arm64_norm, wp_norm, hvregs']⟩
                  have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
                  have hres_next : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
                      (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                      (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField (rest'.length - limit) m rest' limit 97).map
                        (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
                    rw [hres_cur, hloop_ok, hsf]; rfl
                  exact ih m rest' s'' (by omega) (by omega)
                    (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                    hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hcs''

theorem unchunkedCt1SentMerge_own_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeOwnSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp unchunkedCt1SentMergeOwnSpec unchunkedCt1SentMergeOwnSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hpc : s0.pc = (blkPl_312).base := hpc
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_312).rebase (blkPl_312).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (unchunkedCt1SentMergeOwnSpec A lim) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, h, hFit⟩
  have herr0_exit := @ct1Sent_err0_ret_exit_placed _ M A lim H x st R s0
  have hfrom_exit := @ct1Sent_from_err_exit_cl_placed _ M A lim H hFromCall x st R s0
  have hloop := fun (limit : Nat) (hlim_lt : limit < 2 ^ 63) =>
    @ct1Sent_loop_ok_cl_placed _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall
      x st R s0 limit hFit hsp_align h hlim_lt
  have hsaved :
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      unchunkedSavedRegs s0.sp s0 := Entails.refl _
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    let x_dv0 : DecodeVarintSlowGhost := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, unchunkedMergeBelow_leaf s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
      apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20
      apply SepWP.exists_elim; intro v19
      wp_steps
      apply SepWP.fold hsaved (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (spec := decodeVarint2Spec A lim) (x := (x_dv0, st))
        (ret_pc := entry + 52#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [State.spAligned, arm64_norm, wp_norm]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm])
        (by exact ⟨by simp only [arm64_norm, wp_norm, h_3], h,
          by simpa only [AllocCostModel.stepEvents, List.foldl] using
               fitsEnv_decodeVarint2_of_spqr (f₀ := 0) (by omega) SpqrMergeLoopEnv.nil hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint x.bs with
      | none =>
        have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1Sent_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 120#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
            stackAt_decodeVarint2_raw_eq,
            sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro evs_dv
          wp_focus_pure; intro hsm0
          wp_focus_pure; intro htrm
          wp_focus_pure; intro hevs_dv
          wp_focus_pure; intro hsm1
          (conv => arg 4; simp only [arm64_norm, wp_norm])
          apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
          apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
              (Nat.le_refl 1) SpqrMergeLoopEnv.nil (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              memRegion (s0.sp - 112#64) 48 ∗
              unchunkedMergeBelow s0.sp ∗
              ct1SentErrFrame A lim st 1 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
            (by dsimp only [ct1SentErrFrame]; sep_entail)
          exact herr0_exit hnone (by omega) (Nat.zero_le 2) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm])
            (by simp only [arm64_norm, wp_norm]) hsm1
            ⟨by simp only [arm64_norm, wp_norm, hx24_m],
             by simp only [arm64_norm, wp_norm, hx25_m],
             by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      | some p =>
        rcases p with ⟨len, rest0⟩
        have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
        have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
        have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
        have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
        let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
        by_cases hlt_len : rest0.length < len.toNat
        · have hule := ule_len_of_lt hlt_len hrest0_lt
          have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1Sent_mergeField]
            simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 108#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
              stackAt_decodeVarint2_raw_eq,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; rintro ⟨hsm0, hsm1⟩
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            (conv => arg 4; simp only [arm64_norm, wp_norm])
            apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_112 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl 0) SpqrMergeLoopEnv.nil
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000007#64) ∗
                memRegion (s0.sp - 104#64) 40 ∗
                unchunkedMergeBelow s0.sp ∗
                ct1SentErrFrame A lim st 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
              (by dsimp only [ct1SentErrFrame]; sep_entail)
            exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
            have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf
            conv => rhs; rw [hsuf, List.drop_drop]
            exact congrArg (List.drop · x.bs) (by omega)
          have hres0 : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1Sent_mergeField]
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true,
              ↓reduceIte, proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.Ct1Sent.mergeField
              (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 152#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, x_dv0, hdv0,
              stackAt_decodeVarint2_raw_eq,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro evs_dv
            wp_focus_pure; rintro ⟨hsm0, hsm1⟩
            wp_focus_pure; intro htrm
            wp_focus_pure; intro hevs_dv
            (conv => arg 4; simp only [arm64_norm, wp_norm])
            apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
            apply SepWP.fold (protoUnchunkedCt1SentCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.zero_le (4 * (x.bs.length - rest0.length))) SpqrMergeLoopEnv.nil
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
            wp_steps
            have hsca0 : (x.ptr ↦ₛ x.bs.take (x.bs.length - rest0.length)) ∗
                ((x.slot ↦₆₄ rest0Ptr) ∗ ((x.slot + 8#64) ↦₆₄ BitVec.ofNat 64 rest0.length) ∗ (rest0Ptr ↦ₛ rest0)) ⊢
                sliceCursorAfter x.slot x.ptr x.bs rest0 :=
              Entails.of_eq (sliceCursorAfter_eq_split hrest0_le hrest0_suf).symm
            apply SepWP.fold hsca0 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ct1SentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
              (by dsimp only [ct1SentLoopPre]; sep_entail)
            exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf hres0
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              (by simp only [arm64_norm, wp_norm, hx19_m])
              (by simp only [arm64_norm, wp_norm, hx20_m])
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hsm1, hsub])
              (by simp only [arm64_norm, wp_norm])
              ⟨by simp only [arm64_norm, wp_norm, hx24_m],
               by simp only [arm64_norm, wp_norm, hx25_m],
               by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1Sent_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply sepWPpLscro_of_vm (mid := entry + 108#64)
    by_vm_steps
      (conv => arg 4; rw [stackAt_unchunkedMerge s0.sp, sliceCursorAt, memRegion_48_wtErr112 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v29; apply SepWP.exists_elim; intro v30; apply SepWP.exists_elim; intro v23
      apply SepWP.exists_elim; intro v22; apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v20
      apply SepWP.exists_elim; intro v19
      apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
      apply SepWP.fold
        (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl s0)
          (Nat.le_refl 0) SpqrMergeLoopEnv.nil rfl)
        (by sep_focus)
      wp_steps
      apply SepWP.fold hsaved (by sep_focus)
      apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
      apply SepWP.fold (protoUnchunkedCt1SentCapAt_entails_any A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 112#64) ↦₆₄ 0x8000000000000006#64) ∗
          memRegion (s0.sp - 104#64) 40 ∗
          unchunkedMergeBelow s0.sp ∗
          ct1SentErrFrame A lim st 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.bs)
        (by dsimp only [ct1SentErrFrame]; sep_entail)
      exact hfrom_exit hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm]⟩

theorem unchunkedCt1SentMerge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_312).rebase (blkPl_312).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok ((blkPC_312).rebase (blkPl_312).base H)
      (blkPl_312).base
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  subroutine_ok_unchunkedCt1SentMerge_of_own_placed
    (unchunkedCt1SentMerge_own_cl_placed_ok_of_contracts hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall)

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1SentClPlacedBudget
