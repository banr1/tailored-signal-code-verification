/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Verification of `EpochDirection::merge` (Block `299`)

Proves the budget-threaded loop induction (`epochDirection_loop_ok_cl_placed`) and top-level
subroutine contracts (`epochDirectionMerge_cro_placed_ok_of_contracts`,
`epochDirectionMerge_cl_placed_ok_of_contracts`, `epochDirectionMerge_placed_ok_of_contracts`)
for `EpochDirection::merge` on Block `299`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open CryptoVerification.LibsignalTripleRatchet.Prost (HighCalleeSaved IsDropSuffix decodeVarint_suffix itag_beq_tag_false pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sf_truncate32_ofNat64 skip_suffix sliceCursorAfter_eq_split sliceCursorAt suffix_trans ule_len_of_ge ule_len_of_lt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge (EpochDirectionMergeGhost WppPost blkPC_299 blkPl_299 bv_len_sub_limit codecWireTypeToProto epochDirectionMergeStack epochDirectionPBCapOkAt_entails_epochDirectionPBAt epochDirectionPBCapOkAt_mono epochDirectionPB_mergeField_other epochDirectionPB_mergeField_tag1 epochDirectionPB_mergeField_tag2 epochDirectionPB_mergeField_tag3 memRegion_48_split_96 memRegion_48_wtErr96 mergeBytes_suffix mergeLoopBin mergeLoopBin_lt_limit mergeLoopBin_of_key_ok mergeMessageBin mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField proto_mergeBytes_codec_toOption subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm subroutine_ok_withLsCodeRoLoaded_of_withLscroProp withLscroProp wtErr96_entails_memRegion40 wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Varint (skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux (EpochDirectionLoopEnv EpochDirectionMergeEnv EpochDirectionMergePostEnv EpochDirectionOkEnv decodeVarint2Env_of_none decodeVarint2Env_of_some epochDirectionErrFrame epochDirectionLoopPre epochDirectionMergeSpec epochDirectionMergeSpecOfEnv epochDirection_err0_ret_exit_placed epochDirection_from_err_exit_cl_placed epochDirection_skip_step_cl_placed epochDirection_tag1_varint_step_cl_placed epochDirection_tag1_wt_err_step_cl_placed skipField3Env_of_none subroutine_ok_withLsCodeRoLoaded_epochDirectionMergeOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps (epochDirection_decode_key_step_cl_placed epochDirection_loop_le_exit_cl_placed epochDirection_tag2_step_cl_placed epochDirection_tag3_step_cl_placed subroutine_ok_withLsCodeRoLoaded_of_bare)

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl withLsCodeLoaded)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open scoped CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (EpochDirectionPB)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr (epochDirectionPBAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   fitsEvents_append rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv DecodeErrorPushEnv decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env BytesMerge3EnvCore WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23BudgetAux (mergeBytes_length_sum)

export LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetSteps
  (subroutine_ok_withLsCodeRoLoaded_of_bare
   epochDirection_tag2_step_cl_placed
   epochDirection_tag3_step_cl_placed
   epochDirection_loop_le_exit_cl_placed
   epochDirection_decode_key_step_cl_placed)

private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by cases s; rfl
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local simp, local arm64_norm]
private theorem bv64_sub_zero (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre calleeSavedVRegs_setMem_pre

/-! ## Main Loop Induction & Top-Level Block `299` Verification -/

/-- Code-loaded placed main loop induction for `EpochDirection::merge` (Block `299`). -/
theorem epochDirection_loop_ok_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : EpochDirectionMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : EpochDirectionPB) (cur : List (BitVec 8)) (st_cur : M.σ) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      FitsEnv M lim st_cur (EpochDirectionLoopEnv cur.length) →
      ((mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none →
        ∀ evs_rem, EpochDirectionLoopEnv cur.length evs_rem →
          ∃ evs, PostEnv x evs ∧ M.stepEvents evs_rem st_cur = M.stepEvents evs st0) →
      (∀ m_out rest_out,
        (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
          some (m_out, rest_out) →
        ∀ evs_ok, EpochDirectionOkEnv cur.length (cur.length - limit) evs_ok →
          ∃ evs, PostEnv x evs ∧ M.stepEvents evs_ok st_cur = M.stepEvents evs st0) →
      (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
        (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (cur.length - limit) m cur limit 97).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_299).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_299).rebase (blkPl_299).base H) (s0.readReg64 Reg.lr) s
        (epochDirectionLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur st_cur s hcur_n hcur_le hcur_suf hFit_cur hlift_err hlift_ok hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    exact epochDirection_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hFit_cur hlift_err hlift_ok hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur st_cur s hcur_n hcur_le hcur_suf hFit_cur hlift_err hlift_ok hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact epochDirection_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hFit_cur hlift_err hlift_ok hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine epochDirection_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hFit_cur hlift_err hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_succ_le_cur : rest.length + 1 ≤ cur.length := hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hFit_rest_succ : FitsEnv M lim st_cur (EpochDirectionLoopEnv (rest.length + 1)) :=
        fun evs he => hFit_cur evs (he.mono hrest_succ_le_cur)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 97)
        protoPrefixStep_epochDirectionPB_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag1] at hloop_ok
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 284#64) hinv'
        (conv => arg 4; dsimp only [epochDirectionLoopPre])
        wp_steps_sync_pool ((blkPl_299).base + 284#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinv'
        apply SepWPp.weaken_pre
          (P' := epochDirectionLoopPre A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
          (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; sep_ac_rfl))
        by_cases hiwt : iwt = .varint
        · subst hiwt
          have hnone_dv : decodeVarint rest = none →
              (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hdv; simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_none]
          refine epochDirection_tag1_varint_step_cl_placed (limit := limit) hPushCall hVarintCall
            hsp_align hrest_le hrest_lt hrest_suf
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeVarint2 rest hFit_cur)
            (fun _ => LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_push0_after_from hFit_cur)
            (fun hdv evs_p hp => by
              obtain ⟨evs, hevs_post, hst_eq⟩ :=
                hlift_err (hnone_dv hdv) (rustAllocEvents 72 8 ++ evs_p) (.errFromPush hp)
              exact ⟨evs, hevs_post, (M.stepEvents_append (rustAllocEvents 72 8) evs_p st_cur).symm.trans hst_eq⟩)
            hnone_dv
            (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19'])
            (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21'])
            (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := decodeVarint_length hdv
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hrest'_le_cur : rest'.length ≤ cur.length := Nat.le_trans hrest'_le_rest hrest_le_cur
          have hres_next : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest'.length - limit) { m with ctr := v.truncate 32 } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, eq_self, ↓reduceIte, hdv, Option.map_some]
          exact ih { m with ctr := v.truncate 32 } rest' st_cur s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (decodeVarint_suffix hdv))
            (fun evs he => hFit_cur evs (he.mono hrest'_le_cur))
            (fun hnone evs_rem he_rem => hlift_err hnone evs_rem (he_rem.mono hrest'_le_cur))
            (fun m_out rest_out hsome evs_ok he_ok =>
              hlift_ok m_out rest_out hsome evs_ok (he_ok.mono hrest'_le_cur (by omega)))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hnone_wt : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            simp only [hres_cur, hloop_ok, hiwt, ↓reduceIte, Option.map_none]
          exact epochDirection_tag1_wt_err_step_cl_placed hFromCall hPushCall hiwt
            hsp_align hrest_le hrest_suf
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit_cur)
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_push0_after_from hFit_cur)
            (fun evs_p hp => by
              obtain ⟨evs, hevs_post, hst_eq⟩ :=
                hlift_err hnone_wt (rustAllocEvents 72 8 ++ evs_p) (.errFromPush hp)
              exact ⟨evs, hevs_post, (M.stepEvents_append (rustAllocEvents 72 8) evs_p st_cur).symm.trans hst_eq⟩)
            hnone_wt
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag2, proto_mergeBytes_codec_toOption] at hloop_ok
          apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 260#64) hinv'
          (conv => arg 4; dsimp only [epochDirectionLoopPre])
          wp_steps_sync_pool ((blkPl_299).base + 260#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          apply SepWPp.weaken_pre
            (P' := epochDirectionLoopPre A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; sep_ac_rfl))
          have hnone_mb : mergeBytes iwt rest = none →
              (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          refine epochDirection_tag2_step_cl_placed (limit := limit) hPushCall hBytesCall
            hsp_align hrest_le hrest_lt hrest_suf hFit_rest_succ
            (fun hmb evs_rem he_rem => hlift_err (hnone_mb hmb) evs_rem (he_rem.mono hrest_succ_le_cur))
            hnone_mb
            (fun v rest' evs_bm effCap s'' hmb heff_le hbm_eff hFit_next
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
            (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19'])
            (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21'])
            (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hsum : 1 + v.length + rest'.length ≤ rest.length := mergeBytes_length_sum hmb
          have hrest'_le_rest : rest'.length ≤ rest.length := by omega
          have hres_next : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
              (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest'.length - limit) { m with next := v } rest' limit 97).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with next := v } rest' (M.stepEvents evs_bm st_cur) s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            (fun evs he => hFit_next evs (he.mono hrest'_le_rest))
            (fun hnone evs_rem he_rem => by
              have he_step : EpochDirectionLoopEnv cur.length (evs_bm ++ evs_rem) :=
                (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionLoopEnv.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff
                  (he_rem.mono hrest'_le_rest)).mono hrest_succ_le_cur
              obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_err hnone (evs_bm ++ evs_rem) he_step
              exact ⟨evs, hevs_post, (M.stepEvents_append evs_bm evs_rem st_cur).symm.trans hst_eq⟩)
            (fun m_out rest_out hsome evs_ok he_ok => by
              have hlim_le_rest' : limit ≤ rest'.length := by
                by_contra hlt_r
                have hlt_r' : rest'.length < limit := by omega
                rw [hres_next, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_r', Option.map_none] at hsome
                cases hsome
              have he_step : EpochDirectionOkEnv cur.length (cur.length - limit) (evs_bm ++ evs_ok) :=
                (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionOkEnv.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff
                  (he_ok.mono hrest'_le_rest (Nat.le_refl _))).mono hrest_succ_le_cur (by omega)
              obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_ok m_out rest_out hsome (evs_bm ++ evs_ok) he_step
              exact ⟨evs, hevs_post, (M.stepEvents_append evs_bm evs_ok st_cur).symm.trans hst_eq⟩)
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hloop_ok; rw [epochDirectionPB_mergeField_tag3, proto_mergeBytes_codec_toOption] at hloop_ok
            apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 236#64) hinv'
            (conv => arg 4; dsimp only [epochDirectionLoopPre])
            wp_steps_sync_pool ((blkPl_299).base + 236#64)
            simp only [State.setMem_setMem]
            wp_reach; intro hinv'
            apply SepWPp.weaken_pre
              (P' := epochDirectionLoopPre A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; sep_ac_rfl))
            have hnone_mb : mergeBytes iwt rest = none →
                (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
            refine epochDirection_tag3_step_cl_placed (limit := limit) hPushCall hBytesCall
              hsp_align hrest_le hrest_lt hrest_suf hFit_rest_succ
              (fun hmb evs_rem he_rem => hlift_err (hnone_mb hmb) evs_rem (he_rem.mono hrest_succ_le_cur))
              hnone_mb
              (fun v rest' evs_bm effCap s'' hmb heff_le hbm_eff hFit_next
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19'])
              (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21'])
              (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv'
            have hsum : 1 + v.length + rest'.length ≤ rest.length := mergeBytes_length_sum hmb
            have hrest'_le_rest : rest'.length ≤ rest.length := by omega
            have hres_next : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest'.length - limit) { m with prev := v } rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              simp only [hres_cur, hloop_ok, hmb, Option.map_some]
            exact ih { m with prev := v } rest' (M.stepEvents evs_bm st_cur) s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
              (fun evs he => hFit_next evs (he.mono hrest'_le_rest))
              (fun hnone evs_rem he_rem => by
                have he_step : EpochDirectionLoopEnv cur.length (evs_bm ++ evs_rem) :=
                  (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionLoopEnv.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff
                    (he_rem.mono hrest'_le_rest)).mono hrest_succ_le_cur
                obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_err hnone (evs_bm ++ evs_rem) he_step
                exact ⟨evs, hevs_post, (M.stepEvents_append evs_bm evs_rem st_cur).symm.trans hst_eq⟩)
              (fun m_out rest_out hsome evs_ok he_ok => by
                have hlim_le_rest' : limit ≤ rest'.length := by
                  by_contra hlt_r
                  have hlt_r' : rest'.length < limit := by omega
                  rw [hres_next, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_r', Option.map_none] at hsome
                  cases hsome
                have he_step : EpochDirectionOkEnv cur.length (cur.length - limit) (evs_bm ++ evs_ok) :=
                  (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.EpochDirectionOkEnv.stepBytes iwt effCap rest (Nat.le_refl _) heff_le hbm_eff
                    (he_ok.mono hrest'_le_rest (Nat.le_refl _))).mono hrest_succ_le_cur (by omega)
                obtain ⟨evs, hevs_post, hst_eq⟩ := hlift_ok m_out rest_out hsome (evs_bm ++ evs_ok) he_step
                exact ⟨evs, hevs_post, (M.stepEvents_append evs_bm evs_ok st_cur).symm.trans hst_eq⟩)
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
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
            rw [epochDirectionPB_mergeField_other m iwt rest 97 hitag_lt htag1 htag2 htag3] at hloop_ok
            apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 140#64) hinv'
            (conv => arg 4; dsimp only [epochDirectionLoopPre])
            wp_steps_sync_pool ((blkPl_299).base + 140#64)
            simp only [State.setMem_setMem]
            wp_reach; intro hinv'
            apply SepWPp.weaken_pre
              (P' := epochDirectionLoopPre A lim st_cur s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
              (Entails.of_eq (by dsimp only [epochDirectionLoopPre]; sep_ac_rfl))
            have hnone_sf : skipField (2 * rest.length + 2) 97 (key.toNat / 8) iwt rest = none →
                (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
              intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
            refine epochDirection_skip_step_cl_placed (limit := limit) hSkipCall
              hsp_align hrest_le hrest_lt hrest_suf hitag_lt
              (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_skipField3 _ hFit_cur)
              (fun hsf evs_sf hevs_sf => by
                have heq : evs_sf = rustAllocEvents 72 8 := skipField3Env_of_none hsf hevs_sf
                exact hlift_err (hnone_sf hsf) evs_sf (heq ▸ .errFrom))
              hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp'])
              (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv'
            have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
            have hrest'_le_cur : rest'.length ≤ cur.length := Nat.le_trans hrest'_le_rest hrest_le_cur
            have hres_next : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
                (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest'.length - limit) m rest' limit 97).map
                  (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
              rw [hres_cur, hloop_ok, hsf]; rfl
            exact ih m rest' st_cur s'' (by omega) (by omega)
              (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
              (fun evs he => hFit_cur evs (he.mono hrest'_le_cur))
              (fun hnone evs_rem he_rem => hlift_err hnone evs_rem (he_rem.mono hrest'_le_cur))
              (fun m_out rest_out hsome evs_ok he_ok =>
                hlift_ok m_out rest_out hsome evs_ok (he_ok.mono hrest'_le_cur (by omega)))
              hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-- `withLsCodeRoLoaded`-callee contract-parameterized `[LibsignalPlacement]` verification of
`EpochDirection::merge` (Block `299`). -/
theorem epochDirectionMerge_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp epochDirectionMergeSpec epochDirectionMergeSpecOfEnv
  wpp_init p s0
  rcases p with ⟨x, st0⟩
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp; intro hinv0
  replace hpc : s0.pc = (blkPl_299).base := hpc
  change SepWPp _ _ _ _
    (WppPost (epochDirectionMergeSpecOfEnv A lim EpochDirectionMergeEnv EpochDirectionMergePostEnv) (x, st0) R s0)
    (WppBudgetPanic (epochDirectionMergeSpecOfEnv A lim EpochDirectionMergeEnv EpochDirectionMergePostEnv) (x, st0) R s0)
  have hFit0 : FitsEnv M lim st0 (EpochDirectionLoopEnv x.bs.length) := h
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), skipBelow3_leaf s0.sp 98 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    wp_reach; intro hinv0
    refine CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_299).base + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      rfl ⟨by simp only [arm64_norm, h_3], h_4, LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeVarint2 x.bs hFit0⟩
      (by sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 116#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      have hevs_eq : evs_dv = rustAllocEvents 72 8 := decodeVarint2Env_of_none hdv0 hevs_dv
      conv => arg 4; simp only [arm64_norm]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
      apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps_sync_pool ((blkPl_299).base + 116#64)
      simp only [State.setMem_setMem]
      wp_reach; intro _hinvm'
      refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
        (epochDirection_err0_ret_exit_placed hnone
          ⟨evs_dv, by simp only [EpochDirectionMergePostEnv, hnone, hevs_eq]; exact .errFrom, rfl⟩
          hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
          (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) hsm1
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩)
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0, hlt_len]
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
        apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        wp_steps_sync_pool ((blkPl_299).base + 104#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
          (epochDirection_from_err_exit_cl_placed hFromCall hnone
            (by decide : KindNoHeap 0x8000000000000007#64)
            (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit0)
            (fun evs_f hf => ⟨evs_f, by
              dsimp only [DecodeErrorFromEnv] at hf; subst hf
              simp only [EpochDirectionMergePostEnv, hnone]; exact .errFrom, rfl⟩)
            hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
          have hsuf := hrest0_suf; unfold IsDropSuffix at hsuf
          conv => rhs; rw [hsuf, List.drop_drop]
          exact congrArg (List.drop · x.bs) (by omega)
        have hres0 : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption =
            (mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
          simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            proto_decodeVarint_toOption, hdv0, hlt_len, hdrop_eq]
          rcases mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 97 with _ | m' <;> rfl
        apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil : evs_dv = [] := decodeVarint2Env_of_some hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 98 (by decide)) (by sep_focus)
        apply SepWP.fold (epochDirectionPBCapOkAt_mono hrest0_le) (by sep_focus)
        (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
        wp_steps_sync_pool ((blkPl_299).base + 160#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre
          (by rw [epochDirectionLoopPre, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
          (epochDirection_loop_ok_cl_placed hFromCall hPushCall hVarintCall hSkipCall hBytesCall
            hsp_align h_4 hlim_lt rest0.length x.msg rest0 st0 _
            (Nat.le_refl _) hrest0_le hrest0_suf
            (fun evs he => hFit0 evs (he.mono hrest0_le))
            (fun hnone evs_rem he_rem =>
              ⟨evs_rem, by simp only [EpochDirectionMergePostEnv, hnone]; exact he_rem.mono hrest0_le, rfl⟩)
            (fun m_out rest_out hsome evs_ok he_ok => by
              have hrest_out_eq : rest_out = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by
                rw [hres0] at hsome
                rcases hml : mergeLoopBin CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (rest0.length - (rest0.length - len.toNat))
                  x.msg rest0 (rest0.length - len.toNat) 97 with _ | m1
                · rw [hml, Option.map_none] at hsome; cases hsome
                · rw [hml, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
                  exact hsome.2.symm
              have hrest_out_len : rest_out.length = rest0.length - len.toNat := by
                rw [hrest_out_eq, List.length_drop]; omega
              exact ⟨evs_ok, by
                simp only [EpochDirectionMergePostEnv, hsome]
                exact he_ok.mono hrest0_le (by omega), rfl⟩)
            hres0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
            (by simp only [arm64_norm, htrm])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm)
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (mergeMessage CryptoVerification.LibsignalSpqrV1.EpochDirectionPB.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_epochDirectionPB_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.of_sepWP_lscro (mid := (blkPl_299).base + 104#64) hinv0
    (conv => arg 4; rw [epochDirectionMergeStack, stackAt_skipField3 s0.sp 98 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool ((blkPl_299).base + 104#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (epochDirectionPBCapOkAt_entails_epochDirectionPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach; intro hinv0
    refine SepWPp.weaken_pre (by dsimp only [epochDirectionErrFrame]; sep_entail)
      (epochDirection_from_err_exit_cl_placed hFromCall hnone
        (by decide : KindNoHeap 0x8000000000000006#64)
        (LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudgetAux.FitsEnv.epochDirection_decodeErrorFrom hFit0)
        (fun evs_f hf => ⟨evs_f, by
          dsimp only [DecodeErrorFromEnv] at hf; subst hf
          simp only [EpochDirectionMergePostEnv, hnone]; exact .errFrom, rfl⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm]⟩ hinv0)

/-- Code-loaded (`withLsCodeLoaded` on `261/257/291/263` + `withLsCodeRoLoaded` on `290`)
contract-parameterized `[LibsignalPlacement]` verification of `EpochDirection::merge` (Block `299`). -/
theorem epochDirectionMerge_cl_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)) :=
  epochDirectionMerge_cro_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded_mm hSkipCall)
    hBytesCall

/-- Bare-callee (`261/257/291/263`) + `withLsCodeRoLoaded` (`290`) contract-parameterized
`[LibsignalPlacement]` verification of `EpochDirection::merge` (Block `299`). -/
theorem epochDirectionMerge_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (decodeErrorFromBudgetSpec M A lim))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (decodeErrorPushBudgetSpec M A lim))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (decodeVarint2Spec A lim))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (skipField3Spec A lim))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim)) :=
  epochDirectionMerge_cro_placed_ok_of_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_bare hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_bare hSkipCall)
    hBytesCall

/-- Envelope-parameterized `withLsCodeRoLoaded` Block `299` verification corollary. -/
theorem epochDirectionMergeOfEnv_cro_placed_ok_of_contracts [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : EpochDirectionMergeGhost → List AllocEvent → Prop}
    (hpre : ∀ x evs, EpochDirectionMergeEnv x evs → PreEnv x evs)
    (hpost : ∀ x evs, EpochDirectionMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_299).rebase (blkPl_299).base H) (blkPl_299).base
      (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpecOfEnv A lim PreEnv PostEnv)) :=
  subroutine_ok_withLsCodeRoLoaded_epochDirectionMergeOfEnv hpre hpost
    (epochDirectionMerge_cro_placed_ok_of_contracts
      hFromCall hPushCall hVarintCall hSkipCall hBytesCall)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirectionBudget
