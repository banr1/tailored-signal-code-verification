/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthStepsR
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Tight & Base `ProtoAuthenticator::merge` Verification (`Block 295`)

Verifies `ProtoAuthenticator::merge` (Block `295`) both against the general loop envelope
`MergeBaseBudget.authMergeSpec` and under the zero-capacity canonical tight envelope
`tlb_AuthTightEnvOf` on `tlb_AuthDom`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthCountedR

open Arm64 Arm64.Obj ProofLib SepProp
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification
  (LibsignalHooks LibsignalPlacement blkPC_295 blkPl_295 libsignalSessionLib lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap LibsignalCodeRoLoaded decodeErrorAtStackLen decodeErrorHookStack
   extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (HighCalleeSaved IsDropSuffix decodeVarint_suffix itag_beq_tag_false
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sf_truncate32_ofNat64
   skip_suffix sliceCursorAfter_eq_split sliceCursorAt suffix_trans ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Varint
  (decodeVarint2Stack skipBelow3 skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (SepWPp.call_frame_lscro SepWPp.of_sepWP_lscro bv_len_sub_limit codecWireTypeToProto
   memRegion_48_wtErr96 mergeLoopBin mergeLoopBin_lt_limit mergeLoopBin_of_decodeVarint_none
   mergeLoopBin_of_key_ok mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   protoPrefixStep_protoAuthenticator_mergeField wtErr96_entails_memRegion40
   wt_beq_two_of_lengthDelimited wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.LibsignalSpqrV1 (ProtoAuthenticator)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth
  (AuthMergeGhost WppPost authMergeStack authenticatorPBCapAt
   authenticatorPBCapAt_entails_authenticatorPBAt authenticatorPBCapAt_mono bv64_add_zero
   bv64_sub_zero memRegion_48_split_96 mergeBytes_length mergeBytes_suffix
   protoAuthenticator_mergeField_other protoAuthenticator_mergeField_tag1
   protoAuthenticator_mergeField_tag2)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget fitsEvents_append)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_AuthDom tlb_AuthGuardedEnvOf tlb_AuthMergePlacedTightOk tlb_AuthMergePlacedTightOkOf
   tlb_AuthTightEnvOf tlb_authMergeTightSpecOfEnv tlb_authenticatorZeroCapAt tlb_domHeap_of_dom
   tlb_domHeap_of_not_dom tlb_lenPrefixed tlb_vecU8ZeroCapAt tlb_vecU8ZeroCapAt_entails_cap)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget
  (AuthMergeEnv AuthMergeLoopEnv AuthMergePostEnv FitsEnv.authMergeLoop_mono
   FitsEnv.authMergeLoop_split authMergePostEnv_imp_pre authMergeSpec authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudget
  (SepWPp.to_subroutineOutcome_auth_placed auth_decode_key_step_cl_placed
   auth_loop_le_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
  (authBudgetErrFrame authBudgetLoopPre auth_err0_ret_exit_placed auth_from_err_exit_cl_placed
   auth_skip_step_cl_placed stepEvents_append)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (WppBudgetPanic bytesMerge3RawBudgetSpec wppBudgetPanic_false)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthStepsR
  (e2ar_authLoopPre e2ar_authMergeLoopEnv_of_bytesMerge3 e2ar_authMergeLoopEnv_of_bytesMerge3_none
   e2ar_authMergeLoopEnv_of_bytesMerge3_some e2ar_authMergeLoopEnv_of_decodeErrorFrom
   e2ar_authMergeLoopEnv_of_decodeVarint2 e2ar_authMergeLoopEnv_of_pushMerge0
   e2ar_authMergeLoopEnv_of_skipField3 e2ar_auth_key_some_step e2ar_auth_ret_exit
   e2ar_auth_tag1_merge_step_cl_placed e2ar_auth_tag1_zero_step
   e2ar_auth_tag2_merge_step_cl_placed e2ar_auth_tag2_zero_step
   e2ar_mergeMessage_authenticator_lenPrefixed e2ar_vecU8CapAt e2ar_vecU8CapAt_mono)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateTightCountR
  (e2ar_decodeVarint2Env_some_nil e2ar_decodeVarint_encodeKey e2ar_decodeVarint_lenPrefixed
   e2ar_encodeBytesUncond_eq_key_lenPrefixed e2ar_mergeBytes_lenPrefixed
   e2ar_raw_lt_of_lenPrefixed_lt)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

private theorem e2ar_sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl
private theorem e2ar_pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl
private theorem e2ar_status_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).status = s.status := by cases s; rfl
private theorem e2ar_pstate_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).pstate = s.pstate := by cases s; rfl
private theorem e2ar_trace_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).trace = s.trace := by cases s; rfl
private theorem e2ar_readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem e2ar_readReg32_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem e2ar_readReg_setMem_pre (s : State) (m : Memory) (w : Width) (r : Reg) :
    (s.setMem m).readReg w r = s.readReg w r := by cases s; rfl
private theorem e2ar_calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt?
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  for pfx in [`CryptoVerification.SpqrV1.Kdf,
      `CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof] do
    for sfx in ["sp_sub_688_eq_hsp", "sp_add_neg688_eq_hsp",
        "sp_sub_96_eq_hsp_592", "sp_add_neg96_eq_hsp_592",
        "hsp_592_sub_592_eq_hsp", "hsp_592_add_neg592_eq_hsp",
        "hsp_add_688_sub_688", "hsp_592_add_96_eq_sp"] do
      let nm := Lean.Name.str pfx sfx
      if env.contains nm then
        try Lean.Attribute.erase nm `arm64_norm catch _ => pure ()
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  e2ar_sp_setMem_pre e2ar_pc_setMem_pre e2ar_status_setMem_pre e2ar_pstate_setMem_pre
  e2ar_trace_setMem_pre e2ar_readReg64_setMem_pre e2ar_readReg32_setMem_pre
  e2ar_readReg_setMem_pre e2ar_calleeSavedVRegs_setMem_pre

private theorem e2ar_to_subroutineOutcome_auth_tight [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    {x : AuthMergeGhost} {st0 : M.σ} {s0 : State} {P R : SepProp}
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (WppPost (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
      (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (tlb_authMergeTightSpecOfEnv A lim PreEnv PostEnv))
        (x, st0) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨hpan, P_f, hmf, hpanic⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hpanic hmf⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## 1. `MergeBaseBudget.authMergeSpec` Producer (`Block 295` Unconditional Fallback) -/

theorem e2ar_auth_loop_base_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : AuthMergeGhost} {st0 : M.σ} {R : SepProp} {s0 : State} {limit : Nat}
    (hFit0 : FitsEnv M lim st0 (AuthMergeLoopEnv 4 x.bs.length))
    (hPost : ∀ evs, AuthMergePostEnv x evs → PostEnv x evs)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (fuel : Nat) (m : ProtoAuthenticator) (cur : List (BitVec 8))
      (evs_acc : List AllocEvent) (st_cur : M.σ) (s : State),
      cur.length ≤ fuel →
      cur.length ≤ x.bs.length →
      IsDropSuffix x.bs cur →
      st_cur = M.stepEvents evs_acc st0 →
      AuthMergeLoopEnv 0 (x.bs.length - cur.length) evs_acc →
      ((mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit)))) →
      s.pc = (blkPl_295).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
        (authBudgetLoopPre A lim st_cur s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0)
        (WppBudgetPanic (authMergeSpecOfEnv A lim PreEnv PostEnv) (x, st0) R s0) := by
  have hpost_err :
      ∀ {evs : List AllocEvent},
        (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none →
        AuthMergeLoopEnv 4 x.bs.length evs →
        PostEnv x evs := fun hnone hevs => by
    apply hPost
    dsimp only [AuthMergePostEnv]
    rw [hnone]
    exact hevs
  intro fuel
  induction fuel with
  | zero =>
    intro m cur evs_acc st_cur s hcur_fuel hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr _hx19 _hx20 hx21 hx22 hcs hinv
    have hcur0 : cur.length = 0 := Nat.eq_zero_of_le_zero hcur_fuel
    have hFit_rem : FitsEnv M lim st_cur (AuthMergeLoopEnv 4 cur.length) := by
      rw [hst_cur]
      exact FitsEnv.authMergeLoop_split hevs_acc
        (by simpa [show 0 + 4 = 4 from rfl,
          show (x.bs.length - cur.length) + cur.length = x.bs.length by omega] using hFit0)
    have hFit_err1 : FitsEnv M lim st_cur (AuthMergeLoopEnv 1 0) :=
      FitsEnv.authMergeLoop_mono (by decide) (Nat.zero_le _) hFit_rem
    exact auth_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun _ hsome =>
        ⟨evs_acc, hPost _ (by dsimp only [AuthMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
      (fun _ _ hf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf))
      (fun hlt evs_f hf => by
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
        exact ⟨evs_acc ++ evs_f,
          hpost_err hnone
            ((hevs_acc.append (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf)).mono (by decide) (by omega)),
          by rw [hst_cur, stepEvents_append]⟩)
      hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ fuel ih =>
    intro m cur evs_acc st_cur s hcur_fuel hcur_le hcur_suf hst_cur hevs_acc hres_cur
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    have hFit_rem : FitsEnv M lim st_cur (AuthMergeLoopEnv 4 cur.length) := by
      rw [hst_cur]
      exact FitsEnv.authMergeLoop_split hevs_acc
        (by simpa [show 0 + 4 = 4 from rfl,
          show (x.bs.length - cur.length) + cur.length = x.bs.length by omega] using hFit0)
    have hFit_err1 : FitsEnv M lim st_cur (AuthMergeLoopEnv 1 0) :=
      FitsEnv.authMergeLoop_mono (by decide) (Nat.zero_le _) hFit_rem
    have hFit_err2 : FitsEnv M lim st_cur (AuthMergeLoopEnv (1 + 1) 0) :=
      FitsEnv.authMergeLoop_mono (by decide) (Nat.zero_le _) hFit_rem
    by_cases hle_lim : cur.length ≤ limit
    · exact auth_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun _ hsome =>
          ⟨evs_acc, hPost _ (by dsimp only [AuthMergePostEnv]; rw [hsome]; exact hevs_acc), hst_cur⟩)
        (fun _ _ hf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf))
        (fun hlt evs_f hf => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt, Option.map_none]
          exact ⟨evs_acc ++ evs_f,
            hpost_err hnone
              ((hevs_acc.append (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf)).mono (by decide) (by omega)),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine auth_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf
        (fun _ hdv => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeVarint2 hdv))
        (fun hd evs_dv hdv => by
          have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_protoAuthenticator_mergeField hle_lim hd, Option.map_none]
          exact ⟨evs_acc ++ evs_dv,
            hpost_err hnone
              ((hevs_acc.append (e2ar_authMergeLoopEnv_of_decodeVarint2 hdv)).mono (by decide) (by omega)),
            by rw [hst_cur, stepEvents_append]⟩)
        (fun _ hf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf))
        (fun hnone evs_f hf =>
          ⟨evs_acc ++ evs_f,
            hpost_err hnone
              ((hevs_acc.append (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf)).mono (by decide) (by omega)),
            by rw [hst_cur, stepEvents_append]⟩)
        hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hFit_bm1 : FitsEnv M lim st_cur (AuthMergeLoopEnv 1 cur.length) :=
        FitsEnv.authMergeLoop_mono (by decide) (Nat.le_refl _) hFit_rem
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 96)
        protoPrefixStep_protoAuthenticator_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [protoAuthenticator_mergeField_tag1] at hloop_ok
        have hnone_mb : mergeBytes iwt rest = none →
            (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 252#64) hinv'
        conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_295).base + 252#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinv'
        refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
          (e2ar_auth_tag1_merge_step_cl_placed (m := m) (limit := limit) hPushCall hBytesCall
            hsp_align hrest_le hrest_lt hrest_suf
            (fun _ _ _ _ hbm => hFit_bm1 _ (e2ar_authMergeLoopEnv_of_bytesMerge3 hrest_le_cur hbm))
            (fun _ _ evs_bm hmb hevs_bm _ hp =>
              (FitsEnv.authMergeLoop_split (b₁ := 0) (b₂ := 0)
                (e2ar_authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm) hFit_err2) _
                (e2ar_authMergeLoopEnv_of_pushMerge0 hp))
            (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
              ⟨(evs_acc ++ evs_bm) ++ evs_p,
                hpost_err (hnone_mb hmb)
                  (((hevs_acc.append (e2ar_authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm)).append
                    (e2ar_authMergeLoopEnv_of_pushMerge0 hp)).mono (by decide) (by omega)),
                by simp only [hst_cur, stepEvents_append]⟩)
            hnone_mb
            (fun _ _ v rest' evs_bm s'' hmb hevs_bm hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
            (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv')
        have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
        have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with rootKey := v } rest' limit 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hmb, Option.map_some]
        exact ih { m with rootKey := v } rest' (evs_acc ++ evs_bm) (M.stepEvents evs_bm st_cur) s''
          (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
          (by rw [hst_cur, stepEvents_append])
          ((hevs_acc.append (e2ar_authMergeLoopEnv_of_bytesMerge3_some hmb hevs_bm)).mono
            (Nat.le_refl 0) (by dsimp only; omega))
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [protoAuthenticator_mergeField_tag2] at hloop_ok
          have hnone_mb : mergeBytes iwt rest = none →
              (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 228#64) hinv'
          conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_295).base + 228#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
            (e2ar_auth_tag2_merge_step_cl_placed (m := m) (limit := limit) hPushCall hBytesCall
              hsp_align hrest_le hrest_lt hrest_suf
              (fun _ _ _ _ hbm => hFit_bm1 _ (e2ar_authMergeLoopEnv_of_bytesMerge3 hrest_le_cur hbm))
              (fun _ _ evs_bm hmb hevs_bm _ hp =>
                (FitsEnv.authMergeLoop_split (b₁ := 0) (b₂ := 0)
                  (e2ar_authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm) hFit_err2) _
                  (e2ar_authMergeLoopEnv_of_pushMerge0 hp))
              (fun _ _ evs_bm evs_p hmb hevs_bm hp =>
                ⟨(evs_acc ++ evs_bm) ++ evs_p,
                  hpost_err (hnone_mb hmb)
                    (((hevs_acc.append (e2ar_authMergeLoopEnv_of_bytesMerge3_none hmb hevs_bm)).append
                      (e2ar_authMergeLoopEnv_of_pushMerge0 hp)).mono (by decide) (by omega)),
                  by simp only [hst_cur, stepEvents_append]⟩)
              hnone_mb
              (fun _ _ v rest' evs_bm s'' hmb hevs_bm hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
              (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv')
          have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with macKey := v } rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with macKey := v } rest' (evs_acc ++ evs_bm) (M.stepEvents evs_bm st_cur) s''
            (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
            (by rw [hst_cur, stepEvents_append])
            ((hevs_acc.append (e2ar_authMergeLoopEnv_of_bytesMerge3_some hmb hevs_bm)).mono
              (Nat.le_refl 0) (by dsimp only; omega))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
        · have hitag_lt : key.toNat / 8 < 2 ^ 32 := by omega
          obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 hitag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 hitag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by
            rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by
            simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by
            simp only [bne, hb2_2, Bool.not_false]
          rw [protoAuthenticator_mergeField_other m iwt rest 96 hitag_lt htag1 htag2] at hloop_ok
          have hnone_sf : skipField (2 * rest.length + 2) 96 (key.toNat / 8) iwt rest = none →
              (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 140#64) hinv'
          conv => arg 4; rw [authBudgetLoopPre]; simp only [sepConj_assoc]
          wp_steps_sync_pool ((blkPl_295).base + 140#64)
          simp only [State.setMem_setMem]
          wp_reach; intro hinv'
          refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetLoopPre]; sep_ac_rfl))
            (auth_skip_step_cl_placed (m := m) (limit := limit) hSkipCall hsp_align hrest_le hrest_lt hrest_suf hitag_lt
              (fun _ hsf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_skipField3 hsf))
              (fun hsf evs_sf hevs_sf =>
                ⟨evs_acc ++ evs_sf,
                  hpost_err (hnone_sf hsf)
                    ((hevs_acc.append (e2ar_authMergeLoopEnv_of_skipField3 hevs_sf)).mono (by decide) (by omega)),
                  by rw [hst_cur, stepEvents_append]⟩)
              hnone_sf
              (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
              (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
              (by simp only [arm64_norm, hx0'])
              (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64])
              (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
              ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
               by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
               by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
               by simp only [arm64_norm, hvregs']⟩ hinv')
          have hrest'_le_rest : rest'.length ≤ rest.length :=
            (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hres_next : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) m rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            rw [hres_cur, hloop_ok, hsf]; rfl
          exact ih m rest' evs_acc st_cur s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest
              ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            hst_cur (hevs_acc.mono (Nat.le_refl 0) (by omega))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

theorem e2ar_authMergeBase_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthMergePostEnv x evs → PostEnv x evs)
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align_st hL => ?_
  obtain ⟨hinv0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [authMergeSpecOfEnv] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h_1, h_2, h_3, h, hFit_pre⟩, hm⟩ := hpre
  change (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat at h_1
  change s0.readReg64 (Reg.gpr 1#5) = x.msgPtr at h_2
  change s0.readReg64 (Reg.gpr 2#5) = x.bufRef at h_3
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := by
    rw [State.spAligned] at hsp_align_st; exact hsp_align_st
  have hFit0 : FitsEnv M lim st0 (AuthMergeLoopEnv 4 x.bs.length) :=
    hFit_pre.mono (hPre x)
  have hFit_err1 : FitsEnv M lim st0 (AuthMergeLoopEnv 1 0) :=
    FitsEnv.authMergeLoop_mono (by decide) (Nat.zero_le _) hFit0
  have hpost_err0 :
      ∀ (hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
        {evs : List AllocEvent},
        AuthMergeLoopEnv 1 0 evs →
        PostEnv x evs := fun hnone {_} hevs => by
    apply hPost x
    dsimp only [AuthMergePostEnv]
    rw [hnone]
    exact hevs.mono (by decide) (Nat.zero_le _)
  refine Exists.elim (SepWPp.to_subroutineOutcome_auth_placed hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps_sync_pool (lsmpl.base 291)
    simp only [State.setMem_setMem]
    wp_reach; intro hinv0
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
      (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
      (ret_pc := (blkPl_295).base + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      rfl
      ⟨by simp only [arm64_norm, h_3], h,
       fun _ hdv => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeVarint2 hdv)⟩
      (by dsimp only [sliceCursorAt]; sep_focus)
      (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
      (fun _ _ => wppBudgetPanic_false) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 116#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
        show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro evs_dv
      wp_focus_pure; intro hsm0
      wp_focus_pure; intro htrm
      wp_focus_pure; intro hevs_dv
      wp_focus_pure; intro hsm1
      conv => arg 4; simp only [arm64_norm]
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps_sync_pool ((blkPl_295).base + 116#64)
      simp only [State.setMem_setMem]
      wp_reach; intro _hinvm'
      refine SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
          skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim (M.stepEvents evs_dv st0) s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
      exact auth_err0_ret_exit_placed hnone
        ⟨evs_dv, hpost_err0 hnone (e2ar_authMergeLoopEnv_of_decodeVarint2 hevs_dv), rfl⟩
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm]) hsm1
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h)
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil := e2ar_decodeVarint2Env_some_nil hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_stk0
        wp_steps_sync_pool ((blkPl_295).base + 100#64)
        simp only [State.setMem_setMem]
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm'
        refine SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗ authBudgetErrFrame A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl)) ?_
        exact auth_from_err_exit_cl_placed hFromCall hnone
          (by decide : KindNoHeap 0x8000000000000007#64)
          (fun _ hf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf))
          (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf), rfl⟩)
          hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm'
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96 with _ | m' <;> rfl
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
          show 0x40 + (0x40 + decodeErrorHookStack) = decodeVarint2Stack from rfl,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_dv
        wp_focus_pure; rintro ⟨hsm0, hsm1⟩
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_dv
        have hevs_nil := e2ar_decodeVarint2Env_some_nil hdv0 hevs_dv
        subst hevs_nil
        conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc]
        wp_steps_sync_pool ((blkPl_295).base + 160#64)
        simp only [State.setMem_setMem]
        wp_reach; intro hinvm
        refine SepWPp.weaken_pre (P' :=
          authBudgetLoopPre A lim st0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (Entails.of_eq (by
            dsimp only [authBudgetLoopPre]
            rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
            sep_ac_rfl)) ?_
        exact e2ar_auth_loop_base_cl_placed hFromCall hPushCall hVarintCall hSkipCall hBytesCall
          hFit0 (hPost x) hsp_align h hlim_lt
          rest0.length x.msg rest0 [] st0 _ (Nat.le_refl _) hrest0_le hrest0_suf rfl .nil hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps_sync_pool ((blkPl_295).base + 100#64)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach; intro hinv0'
    refine SepWPp.weaken_pre (Entails.of_eq (by dsimp only [authBudgetErrFrame]; sep_ac_rfl))
      (auth_from_err_exit_cl_placed (m := x.msg) (v_stk0 := v_wt0) hFromCall hnone
        (by decide : KindNoHeap 0x8000000000000006#64)
        (fun _ hf => hFit_err1 _ (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf))
        (fun evs_f hf => ⟨evs_f, hpost_err0 hnone (e2ar_authMergeLoopEnv_of_decodeErrorFrom hf), rfl⟩)
        hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [arm64_norm],
         by simp only [arm64_norm]⟩ hinv0')

/-- Code-loaded verification of Block `295` (`ProtoAuthenticator::merge`) against
`MergeBaseBudget.authMergeSpec A lim` on `(blkPC_295).rebase (blkPl_295).base H`. -/
theorem e2ar_authMergeBase_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  e2ar_authMergeBase_cro_placed_ok (fun _ _ h => h) (fun _ _ h => h)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkipCall)
    hBytesCall

private theorem e2ar_blkPC295_eq_blockProgram [LibsignalPlacement] (H : LibsignalHooks) :
    (blkPC_295).rebase (blkPl_295).base H = libsignalSessionLib.blockProgram lsmpl 295 H :=
  (CryptoVerification.instIsLsBlockProg_295 H).eq_blockProgram

private theorem e2ar_blockLib_externs_eq {i : Nat}
    (h : (CryptoVerification.lsBlocksTree.getFast? i).map (·.externs) =
      some CryptoVerification.libsignalSessionExterns := by rfl) :
    (libsignalSessionLib.blockLib i).text.externs = CryptoVerification.libsignalSessionExterns := by
  cases hget : CryptoVerification.lsBlocksTree.getFast? i with
  | none => rw [hget] at h; cases h
  | some blk =>
    rw [hget, Option.map_some, Option.some.injEq] at h
    have hlib := CryptoVerification.blockLib_eq_of_lsBlocksTree hget (lib :=
      { name := "libsignalSession", text := blk,
        data := CryptoVerification.libsignalSessionData,
        exports := CryptoVerification.libsignalSessionMultiLib.exports }) rfl
    rw [← hlib]
    exact h

private theorem e2ar_blockProgram_cl_of_block [LibsignalPlacement] {α : Type}
    {i j : Nat} {H : LibsignalHooks} {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeLoaded lsmpl spec))
    (hj : j < 624 := by decide)
    (hj_unmut : (j ∈ CryptoVerification.libsignalMutatedBlocks) = false := by decide)
    (hext_i : (CryptoVerification.lsBlocksTree.getFast? i).map (·.externs) =
      some CryptoVerification.libsignalSessionExterns := by rfl)
    (hext_j : (CryptoVerification.lsBlocksTree.getFast? j).map (·.externs) =
      some CryptoVerification.libsignalSessionExterns := by rfl) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) entry
      (withLsCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := CryptoVerification.extract_withLsCodeLoaded hpre
  have hQL := hcl0 j hj hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc,
      (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      (libsignalSessionLib.blockProgram lsmpl i H).externAt? pc := fun pc => by
    rw [LibsignalBinary.Proofs.Placed.PlacedCallSym.ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl
      H Syscall.standard
      ((e2ar_blockLib_externs_eq hext_j).trans (e2ar_blockLib_externs_eq hext_i).symm)]
  exact reaches_outcome_steps (Steps.of_sameHooks hext rfl hstepsQ) (reaches_outcome.of_outcome hout)

private theorem e2ar_blockProgram_cro_of_block [LibsignalPlacement] {α : Type}
    {i j : Nat} {H : LibsignalHooks} {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) entry
      (withLsCodeRoLoaded lsmpl spec))
    (hj : j < 624 := by decide)
    (hj_unmut : (j ∈ CryptoVerification.libsignalMutatedBlocks) = false := by decide)
    (hext_i : (CryptoVerification.lsBlocksTree.getFast? i).map (·.externs) =
      some CryptoVerification.libsignalSessionExterns := by rfl)
    (hext_j : (CryptoVerification.lsBlocksTree.getFast? j).map (·.externs) =
      some CryptoVerification.libsignalSessionExterns := by rfl) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl i H) entry
      (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcro0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL := hcro0.1 j hj hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc,
      (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      (libsignalSessionLib.blockProgram lsmpl i H).externAt? pc := fun pc => by
    rw [LibsignalBinary.Proofs.Placed.PlacedCallSym.ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl
      H Syscall.standard
      ((e2ar_blockLib_externs_eq hext_j).trans (e2ar_blockLib_externs_eq hext_i).symm)]
  exact reaches_outcome_steps (Steps.of_sameHooks hext rfl hstepsQ) (reaches_outcome.of_outcome hout)

/-- `blockProgram lsmpl 295` twin of `e2ar_authMergeBase_cl_placed_ok` (`hAuthBase` in
`ChunkedMergeTightPlacedBudgetA`). -/
theorem e2ar_authMergeBase_at295_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytesCall : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) := by
  have hprog := e2ar_blkPC295_eq_blockProgram (Rust.withPanics ext)
  rw [← hprog] at hFromCall hPushCall hVarintCall hSkipCall hBytesCall ⊢
  exact e2ar_authMergeBase_cl_placed_ok hFromCall hPushCall hVarintCall hSkipCall hBytesCall

/-- Own-block (`261/257/291/263/290`) wrapper producing `hAuthBase` directly. -/
theorem e2ar_authMergeBase_at295_of_own_cl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  e2ar_authMergeBase_at295_cl_placed_ok
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 261) hFrom)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 257) hPush)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 291) hVarint)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 263) hSkip)
    (e2ar_blockProgram_cro_of_block (i := 295) (j := 290) hBytes)

/-! ## 2. Canonical Zero-Cap Execution on `tlb_AuthDom` & Guarded-Tight Producers (`Block 295`) -/

private theorem e2ar_wt_eq_lengthDelimited {wt : WireType}
    (h : codecWireTypeToProto wt = .lengthDelimited) :
    wt = .lengthDelimited := by
  cases wt <;> simp_all [codecWireTypeToProto]

private noncomputable def e2ar_authDomOnlySpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxOps : Nat) :
    Spec (AuthMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.msgPtr ∧
      s.readReg64 .x2 = x.bufRef ∧
      x.bs.length < 2 ^ 63 ∧
      tlb_AuthDom x ∧
      FitsEnv M lim st (tlb_AuthGuardedEnvOf maxOps x)⌝ ∗
      tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr x.msg ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp authMergeStack
  post := (tlb_authMergeTightSpecOfEnv A lim
    (tlb_AuthGuardedEnvOf maxOps) (tlb_AuthGuardedEnvOf maxOps)).post

private theorem e2ar_authDomOnly_cro_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {maxOps : Nat}
    (hOps : 4 ≤ maxOps)
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (e2ar_authDomOnlySpec A lim maxOps)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp_align_st hL => ?_
  obtain ⟨hinv0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [e2ar_authDomOnlySpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨h_1, h_2, h_3, h_4, hDom, hFit_pre⟩, hm⟩ := hpre
  change (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat at h_1
  change s0.readReg64 (Reg.gpr 1#5) = x.msgPtr at h_2
  change s0.readReg64 (Reg.gpr 2#5) = x.bufRef at h_3
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := by
    rw [State.spAligned] at hsp_align_st; exact hsp_align_st
  rcases hDom with ⟨hwt_c, hmsg, pb, rest_out, ⟨hroot32, hmac32⟩, hbs_eq⟩
  have hDom' : tlb_AuthDom x := ⟨hwt_c, hmsg, pb, rest_out, ⟨hroot32, hmac32⟩, hbs_eq⟩
  have hwt_ld : x.wt = .lengthDelimited := e2ar_wt_eq_lengthDelimited hwt_c
  have hFit0 : FitsEnv M lim st0 (tlb_AuthTightEnvOf maxOps) :=
    fun evs ht => hFit_pre evs (Or.inl ⟨hDom', ht⟩)
  have hPost : ∀ evs, tlb_AuthTightEnvOf maxOps evs → tlb_AuthGuardedEnvOf maxOps x evs :=
    fun _ ht => Or.inl ⟨hDom', ht⟩
  have hraw_lt : (ProtoAuthenticator.encodeRaw pb).length < 2 ^ 64 := by
    apply e2ar_raw_lt_of_lenPrefixed_lt (rest := rest_out)
    rwa [← hbs_eq]
  have hsome_auth : (mergeMessage ProtoAuthenticator.mergeField
      (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = some (pb, rest_out) := by
    rw [hwt_c, hmsg, hbs_eq]
    exact e2ar_mergeMessage_authenticator_lenPrefixed pb rest_out 97 (by decide) (hbs_eq ▸ h_4)
  refine Exists.elim (e2ar_to_subroutineOutcome_auth_tight
      (PreEnv := tlb_AuthGuardedEnvOf maxOps) (PostEnv := tlb_AuthGuardedEnvOf maxOps) hm hL ?_)
    fun _ ⟨hsteps, hout⟩ => reaches_outcome_steps hsteps (reaches_outcome.of_outcome hout)
  have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
  have hbeq := wt_beq_two_of_lengthDelimited h_1'
  have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
    simp only [bne, hbeq, Bool.not_true]
  have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
    rw [truncate32_zeroExtend64_and_255_eq, h_1']; decide
  have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
    revert h_1'; bv_bits
  let raw := ProtoAuthenticator.encodeRaw pb
  let rest0 := raw ++ rest_out
  let len0 : BitVec 64 := BitVec.ofNat 64 raw.length
  have hdv0 : decodeVarint x.bs = some (len0, rest0) := by
    rw [hbs_eq]
    exact e2ar_decodeVarint_lenPrefixed raw rest_out
  have hfits_dv0 : FitsEnv M lim st0 (DecodeVarint2Env x.bs) := fun evs he => by
    rw [e2ar_decodeVarint2Env_some_nil hdv0 he]; trivial
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
  (conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
  apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
  wp_steps_sync_pool (lsmpl.base 291)
  simp only [State.setMem_setMem]
  wp_reach; intro hinv0
  refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A lim)
    (x := (⟨x.bufRef, x.slot, x.ptr, x.bs⟩, st0))
    (ret_pc := (blkPl_295).base + 48#64) hVarintCall hinv0
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    rfl ⟨by simp only [arm64_norm, h_3], h_4, hfits_dv0⟩
    (by dsimp only [sliceCursorAt]; sep_focus)
    (fun _ _ _ _ hex => False.elim (not_satisfies_false_sepConj hex))
    (fun _ _ => wppBudgetPanic_false) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, h_2, h_3]
    at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
  have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
  have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_lt_of_le hrest0_lt_bs (Nat.le_of_lt h_4)
  have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
  have hlen0_nat : len0.toNat = raw.length := by
    dsimp only [len0, raw]
    simp only [BitVec.toNat_ofNat]
    omega
  have hlt_len : ¬ rest0.length < len0.toNat := by
    dsimp only [rest0]; rw [List.length_append, hlen0_nat]; omega
  have hule := ule_len_of_ge hlt_len hrest0_lt
  have hsub := bv_len_sub_limit hlt_len
  have hlim_eq : rest0.length - len0.toNat = rest_out.length := by
    dsimp only [rest0]; rw [List.length_append, hlen0_nat]; omega
  have hlim_raw : rest0.length - raw.length = rest_out.length := by
    rw [← hlen0_nat]; exact hlim_eq
  apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
  (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv0,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
  apply SepWP.exists_elim; intro evs_dv
  wp_focus_pure; rintro ⟨hsm0, hsm1⟩
  wp_focus_pure; intro htrm
  wp_focus_pure; intro hevs_dv
  have hevs_nil : evs_dv = [] := e2ar_decodeVarint2Env_some_nil hdv0 hevs_dv
  subst hevs_nil
  conv => arg 4; dsimp only [AllocCostModel.stepEvents, List.foldl]; simp only [arm64_norm]
  apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
  (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
  wp_steps_sync_pool ((blkPl_295).base + 160#64)
  simp only [State.setMem_setMem]
  wp_reach; intro hinvm
  let cur2 := CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 2#32 pb.macKey ++ rest_out
  have hrest0_eq : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField 1#32 pb.rootKey ++ cur2 := by
    dsimp only [rest0, raw, ProtoAuthenticator.encodeRaw, cur2]
    simp only [List.append_assoc]
  have ht1_imp_tight : ∀ evs1, SpqrTightEvs 2 1476 32 evs1 → tlb_AuthTightEnvOf maxOps evs1 :=
    fun _ ht1 => by
      dsimp only [tlb_AuthTightEnvOf]
      exact ht1.mono (by omega) (by decide) (by decide)
  have hFit_t1 : FitsEnv M lim st0 (SpqrTightEvs 2 1476 32) :=
    fun evs1 ht1 => hFit0 evs1 (ht1_imp_tight evs1 ht1)
  suffices hAfter1 : ∀ (evs1 : List AllocEvent) (s1 : State),
      SpqrTightEvs 2 1476 32 evs1 →
      IsDropSuffix x.bs cur2 → cur2.length ≤ x.bs.length →
      s1.pc = (blkPl_295).base + 160#64 →
      s1.status = .Running → s1.sp = s0.sp - 96#64 → s1.trace = s0.trace →
      s1.readReg64 (Reg.gpr 19#5) = x.bufRef → s1.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s1.readReg64 (Reg.gpr 21#5) = x.slot →
      s1.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 rest_out.length →
      HighCalleeSaved s0 s1 → LibsignalCodeRoLoaded lsmpl s1.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s1
        (e2ar_authLoopPre A lim (M.stepEvents evs1 st0) s0 s1 x.bufRef x.slot x.ptr
          (e2ar_vecU8CapAt A.repAlloc x.msgPtr cur2.length pb.rootKey ∗
            tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) ([] : List (BitVec 8)))
          x.bs cur2)
        (WppPost (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf maxOps) (tlb_AuthGuardedEnvOf maxOps)) (x, st0) R s0)
        (WppBudgetPanic (tlb_authMergeTightSpecOfEnv A lim
          (tlb_AuthGuardedEnvOf maxOps) (tlb_AuthGuardedEnvOf maxOps)) (x, st0) R s0) by
    refine SepWPp.weaken_pre
      (P' := e2ar_authLoopPre A lim st0 s0 _ x.bufRef x.slot x.ptr
        (tlb_authenticatorZeroCapAt A.repAlloc x.msgPtr default) x.bs rest0)
      (Entails.of_eq (by
        rw [e2ar_authLoopPre, hmsg, sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        sep_ac_rfl)) ?_
    by_cases hroot_emp : pb.rootKey.isEmpty = true
    · have hroot_nil : pb.rootKey = [] := List.isEmpty_iff.mp hroot_emp
      have hr0_eq : rest0 = cur2 := by
        rw [hrest0_eq, CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hroot_emp]; rfl
      rw [hr0_eq] at hrest0_suf hrest0_le ⊢
      refine SepWPp.weaken_pre ?_
        (hAfter1 [] _ (SpqrTightEvs.nil 2 1476 32) hrest0_suf hrest0_le
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq, hlim_raw])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm)
      dsimp only [e2ar_authLoopPre, tlb_authenticatorZeroCapAt, e2ar_vecU8CapAt,
        AllocCostModel.stepEvents, List.foldl]
      rw [hroot_nil]
      exact sepConj_mono_left (sepConj_mono_left
        (tlb_vecU8ZeroCapAt_entails_cap A.repAlloc x.msgPtr cur2.length []))
    · have hroot_false : pb.rootKey.isEmpty = false := Bool.eq_false_iff.mpr hroot_emp
      let rest1 := tlb_lenPrefixed pb.rootKey cur2
      have hr0_key : rest0 = CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 1#32 .lengthDelimited ++ rest1 := by
        rw [hrest0_eq, CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hroot_false]
        exact e2ar_encodeBytesUncond_eq_key_lenPrefixed 1#32 pb.rootKey cur2
      obtain ⟨key1, hd_k1, hk1⟩ := e2ar_decodeVarint_encodeKey 1#32 .lengthDelimited rest1 (by decide)
      rw [← hr0_key] at hd_k1
      have hmb1 : mergeBytes .lengthDelimited rest1 = some (pb.rootKey, cur2) :=
        e2ar_mergeBytes_lenPrefixed pb.rootKey cur2 (by omega)
      have hgt1 : ¬ rest0.length ≤ rest_out.length := by
        have h1 : rest1.length < rest0.length := decodeVarint_length hd_k1
        have h2 : cur2.length < rest1.length := mergeBytes_length hmb1
        have h3 : rest_out.length ≤ cur2.length := by
          dsimp only [cur2]; simp only [List.length_append]; omega
        omega
      have hrest1_le : rest1.length ≤ x.bs.length :=
        Nat.le_trans (Nat.le_of_lt (decodeVarint_length hd_k1)) hrest0_le
      have hrest1_lt : rest1.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest1_le h_4
      have hrest1_suf : IsDropSuffix x.bs rest1 :=
        suffix_trans hrest0_le hrest0_suf (Nat.le_of_lt (decodeVarint_length hd_k1))
          (decodeVarint_suffix hd_k1)
      have hcur2_le : cur2.length ≤ x.bs.length :=
        Nat.le_trans (Nat.le_of_lt (mergeBytes_length hmb1)) hrest1_le
      have hcur2_suf : IsDropSuffix x.bs cur2 :=
        suffix_trans hrest1_le hrest1_suf (Nat.le_of_lt (mergeBytes_length hmb1))
          (mergeBytes_suffix hmb1)
      have hk1_val : key1.toNat = 10 := by rw [hk1]; decide
      refine e2ar_auth_key_some_step (iwt := .lengthDelimited) hVarintCall hgt1 hsp_align
        hrest0_le hrest0_lt hrest0_suf hd_k1 (by rw [hk1_val]; decide) (by rw [hk1_val]; decide)
        (by rw [hk1_val]) ?_
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub, hlim_eq, hlim_raw])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm
      intro s1' hpc1' hrun1' hsp1' htr1' hx0_1' hx1_1' hx19_1' hx20_1' hx21_1' hx22_1' hcs1' hinv1'
      have hx1_eq : BitVec.ofNat 64 (key1.toNat / 8) = 1#64 := by rw [hk1_val]
      rw [hx1_eq] at hx1_1'
      refine e2ar_auth_tag1_zero_step (m := default) hBytesCall hsp_align hrest1_le hrest1_lt
        hrest1_suf hmb1 hroot32 hFit_t1 ?_
        hpc1' hrun1' hsp1' htr1' hx0_1' hx1_1' hx19_1' hx20_1' hx21_1' hx22_1' hcs1' hinv1'
      intro evs1 s2' ht1 hpc2' hrun2' hsp2' htr2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
      exact hAfter1 evs1 s2' ht1 hcur2_suf hcur2_le
        hpc2' hrun2' hsp2' htr2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
  intro evs1 s1 ht1 hcur2_suf hcur2_le hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
  by_cases hmac_emp : pb.macKey.isEmpty = true
  · have hmac_nil : pb.macKey = [] := List.isEmpty_iff.mp hmac_emp
    have hc2_eq : cur2 = rest_out := by
      dsimp only [cur2]; rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hmac_emp]; rfl
    rw [hc2_eq] at hcur2_suf hcur2_le ⊢
    have hpb_cap :
        e2ar_vecU8CapAt A.repAlloc x.msgPtr rest_out.length pb.rootKey ∗
          tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) ([] : List (BitVec 8)) ⊢
          authenticatorPBCapAt A.repAlloc x.msgPtr rest_out.length pb := by
      unfold authenticatorPBCapAt e2ar_vecU8CapAt
      rw [hmac_nil]
      exact sepConj_mono (Entails.refl _)
        (tlb_vecU8ZeroCapAt_entails_cap A.repAlloc (x.msgPtr + 24#64) rest_out.length [])
    refine SepWPp.weaken_pre
      (by dsimp only [e2ar_authLoopPre]; exact sepConj_mono_left hpb_cap)
      (e2ar_auth_ret_exit (m := pb) (evs := evs1) rfl hsp_align hcur2_le hcur2_suf hsome_auth
        (hPost evs1 (ht1_imp_tight evs1 ht1)) rfl
        hpc1 hrun1 hsp1 htr1 hx21_1 hx22_1 hcs1)
  · have hmac_false : pb.macKey.isEmpty = false := Bool.eq_false_iff.mpr hmac_emp
    have ht12_imp_tight : ∀ evs2, SpqrTightEvs 2 1476 32 evs2 → tlb_AuthTightEnvOf maxOps (evs1 ++ evs2) :=
      fun _ ht2 => by
        dsimp only [tlb_AuthTightEnvOf]
        exact (ht1.append ht2).mono (by omega) (by decide) (by decide)
    have hFit_t2 : FitsEnv M lim (M.stepEvents evs1 st0) (SpqrTightEvs 2 1476 32) :=
      fun evs2 ht2 =>
        ((fitsEvents_append M lim evs1 evs2 st0).mp
          (hFit0 (evs1 ++ evs2) (ht12_imp_tight evs2 ht2))).2
    let rest2 := tlb_lenPrefixed pb.macKey rest_out
    have hc2_key : cur2 = CryptoVerification.LibsignalSpqrV1.Proto.encodeKey 2#32 .lengthDelimited ++ rest2 := by
      dsimp only [cur2, rest2]
      rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeBytesField, hmac_false]
      exact e2ar_encodeBytesUncond_eq_key_lenPrefixed 2#32 pb.macKey rest_out
    obtain ⟨key2, hd_k2, hk2⟩ := e2ar_decodeVarint_encodeKey 2#32 .lengthDelimited rest2 (by decide)
    rw [← hc2_key] at hd_k2
    have hmb2 : mergeBytes .lengthDelimited rest2 = some (pb.macKey, rest_out) :=
      e2ar_mergeBytes_lenPrefixed pb.macKey rest_out (by omega)
    have hcur2_lt : cur2.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur2_le h_4
    have hgt2 : ¬ cur2.length ≤ rest_out.length := by
      have h1 : rest2.length < cur2.length := decodeVarint_length hd_k2
      have h2 : rest_out.length < rest2.length := mergeBytes_length hmb2
      omega
    have hrest2_le : rest2.length ≤ x.bs.length :=
      Nat.le_trans (Nat.le_of_lt (decodeVarint_length hd_k2)) hcur2_le
    have hrest2_lt : rest2.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest2_le h_4
    have hrest2_suf : IsDropSuffix x.bs rest2 :=
      suffix_trans hcur2_le hcur2_suf (Nat.le_of_lt (decodeVarint_length hd_k2))
        (decodeVarint_suffix hd_k2)
    have hro_le : rest_out.length ≤ x.bs.length :=
      Nat.le_trans (Nat.le_of_lt (mergeBytes_length hmb2)) hrest2_le
    have hro_suf : IsDropSuffix x.bs rest_out :=
      suffix_trans hrest2_le hrest2_suf (Nat.le_of_lt (mergeBytes_length hmb2))
        (mergeBytes_suffix hmb2)
    let m1 : ProtoAuthenticator := { rootKey := pb.rootKey, macKey := [] }
    have hk2_val : key2.toNat = 18 := by rw [hk2]; decide
    refine e2ar_auth_key_some_step (iwt := .lengthDelimited) hVarintCall hgt2 hsp_align
      hcur2_le hcur2_lt hcur2_suf hd_k2 (by rw [hk2_val]; decide) (by rw [hk2_val]; decide)
      (by rw [hk2_val]; decide) ?_
      hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1 hinv1
    intro s2' hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
    have hx1_eq : BitVec.ofNat 64 (key2.toNat / 8) = 2#64 := by rw [hk2_val]
    rw [hx1_eq] at hx1_2'
    have hrest2_le_cur2 : rest2.length ≤ cur2.length := Nat.le_of_lt (decodeVarint_length hd_k2)
    refine SepWPp.weaken_pre
      (P' := e2ar_authLoopPre A lim (M.stepEvents evs1 st0) s0 s2' x.bufRef x.slot x.ptr
        (e2ar_vecU8CapAt A.repAlloc x.msgPtr rest2.length m1.rootKey ∗
          tlb_vecU8ZeroCapAt A.repAlloc (x.msgPtr + 24#64) m1.macKey) x.bs rest2)
      (by
        dsimp only [e2ar_authLoopPre, m1]
        exact sepConj_mono_left (sepConj_mono_left
          (e2ar_vecU8CapAt_mono (a := x.msgPtr) (bs := pb.rootKey) hrest2_le_cur2))) ?_
    refine e2ar_auth_tag2_zero_step (m := m1) hBytesCall hsp_align hrest2_le hrest2_lt
      hrest2_suf hmb2 hmac32 hFit_t2 ?_
      hpc2' hrun2' hsp2' htr2' hx0_2' hx1_2' hx19_2' hx20_2' hx21_2' hx22_2' hcs2' hinv2'
    intro evs2 s3' ht2 hpc3' hrun3' hsp3' htr3' hx19_3' hx20_3' hx21_3' hx22_3' hcs3' hinv3'
    have hm1_eq : ({ m1 with macKey := pb.macKey } : ProtoAuthenticator) = pb := by cases pb; rfl
    rw [hm1_eq]
    exact e2ar_auth_ret_exit (m := pb) (evs := evs1 ++ evs2) rfl hsp_align hro_le hro_suf hsome_auth
      (hPost (evs1 ++ evs2) (ht12_imp_tight evs2 ht2))
      (stepEvents_append evs1 evs2 st0).symm
      hpc3' hrun3' hsp3' htr3' hx21_3' hx22_3' hcs3'

/-- Code-loaded Block `295` (`ProtoAuthenticator::merge`) tight producer from `hVarint`, `hBytes`,
and `hAuthBase : subroutine_ok (blockProgram lsmpl 295 _) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))`. -/
theorem e2ar_authMerge_cl_placed_ok_tight_of_base [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {ext : String → Option (State → State)}
    (hOps : 4 ≤ maxOps)
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    tlb_AuthMergePlacedTightOkOf A lim maxOps ext := by
  have hprog := e2ar_blkPC295_eq_blockProgram (Rust.withPanics ext)
  have hVarint' := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarint
  have hBytes' := hBytes
  rw [← hprog] at hVarint' hBytes'
  have hDom295 : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (e2ar_authDomOnlySpec A lim maxOps)) :=
    hprog ▸ e2ar_authDomOnly_cro_placed_ok hOps hVarint' hBytes'
  refine subroutine_ok_intro fun ⟨x, st0⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hDom : tlb_AuthDom x
  · have hpre_dom : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (e2ar_authDomOnlySpec A lim maxOps)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [withLsCodeRoLoaded, tlb_authMergeTightSpecOfEnv,
        e2ar_authDomOnlySpec] at hp ⊢
      rw [tlb_domHeap_of_dom hDom] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, hDom, hp.1.2.2.2.2⟩, hp.2⟩
    exact subroutine_ok_apply_full hDom295 (x, st0) R hpc hrun hpre_dom hsp
  · have hpre_fb : s0.mem ⊨
        (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)).pre (x, st0) s0 ∗ R := by
      obtain ⟨hcro, hp⟩ := extract_withLsCodeRoLoaded hpre
      dsimp only [withLsCodeRoLoaded, tlb_authMergeTightSpecOfEnv,
        authMergeSpec, authMergeSpecOfEnv] at hp ⊢
      rw [tlb_domHeap_of_not_dom hDom] at hp
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcro, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
      refine ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1, hp.1.2.2.2.1, ?_⟩, hp.2⟩
      exact fun evs he => hp.1.2.2.2.2 evs (Or.inr ⟨hDom, he⟩)
    refine reaches_pc_mono
      (subroutine_ok_apply_full hAuthBase (x, st0) R hpc hrun hpre_fb hsp)
      (fun sf _ _ ⟨hpost, hcc⟩ => ⟨?_, hcc⟩)
    dsimp only [withLsCodeRoLoaded, tlb_authMergeTightSpecOfEnv,
      authMergeSpec, authMergeSpecOfEnv] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Entails.sepExists_mono fun evs =>
        Entails.pure_left fun h1 =>
          Entails.pure_right (Or.inr ⟨hDom, authMergePostEnv_imp_pre h1⟩)
            (Entails.refl _)))))) hpost

/-- Specialization of `e2ar_authMerge_cl_placed_ok_tight_of_base` at `maxOps = 4`. -/
theorem e2ar_authMerge_cl_placed_ok_tight_base [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    (hAuthBase : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    tlb_AuthMergePlacedTightOk A lim ext :=
  e2ar_authMerge_cl_placed_ok_tight_of_base (Nat.le_refl 4) hVarint hBytes hAuthBase

/-- Standalone code-loaded Block `295` (`ProtoAuthenticator::merge`) tight producer (`4 ≤ maxOps`)
from `blockProgram lsmpl 295` `withLsCodeLoaded` callees `261`, `257`
(`decodeErrorPushMergeBudgetSpec`), `291`, `263`, and `withLsCodeRoLoaded` callee `290`. -/
theorem e2ar_authMerge_cl_placed_ok_tight_of [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {maxOps : Nat}
    {ext : String → Option (State → State)}
    (hOps : 4 ≤ maxOps)
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    tlb_AuthMergePlacedTightOkOf A lim maxOps ext :=
  e2ar_authMerge_cl_placed_ok_tight_of_base hOps hVarint hBytes
    (e2ar_authMergeBase_at295_cl_placed_ok hFrom hPush hVarint hSkip hBytes)

/-- Standalone code-loaded Block `295` (`ProtoAuthenticator::merge`) tight producer (`maxOps = 4`). -/
theorem e2ar_authMerge_cl_placed_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    tlb_AuthMergePlacedTightOk A lim ext :=
  e2ar_authMerge_cl_placed_ok_tight_of (Nat.le_refl 4) hFrom hPush hVarint hSkip hBytes

/-- Own-block (`261/257/291/263/290`) code-loaded Block `295` tight producer matching
`ChunkedMergeTightPlacedBudgetA` (`hAuthTight` from own-block callees with no `hAuthBase` needed). -/
theorem e2ar_authMerge_own_cl_placed_ok_tight [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A lim)))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim))) :
    tlb_AuthMergePlacedTightOk A lim ext :=
  e2ar_authMerge_cl_placed_ok_tight
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 261) hFrom)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 257) hPush)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 291) hVarint)
    (e2ar_blockProgram_cl_of_block (i := 295) (j := 263) hSkip)
    (e2ar_blockProgram_cro_of_block (i := 295) (j := 290) hBytes)

/-- Plain-callee sibling of `e2ar_authMerge_cl_placed_ok_tight` (accepting either
`SignedDepsBudget.bytesMerge3RawBudgetSpec` or `PolyCommonBudget.bytesMerge3RawBudgetSpec` via
`e2ar_polyBytesMerge_of_signed`, with `decodeErrorPushMergeBudgetSpec` on Block `257`). -/
theorem e2ar_authMerge_placed_ok_tight_pushMerge [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim))
    (hPush : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 257) (decodeErrorPushMergeBudgetSpec M A lim))
    (hVarint : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 291) (decodeVarint2Spec A lim))
    (hSkip : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 263) (skipField3Spec A lim))
    (hBytes : subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim))) :
    tlb_AuthMergePlacedTightOk A lim ext :=
  e2ar_authMerge_cl_placed_ok_tight
    (subroutine_ok_withLsCodeLoaded_of_plain hFrom)
    (subroutine_ok_withLsCodeLoaded_of_plain hPush)
    (subroutine_ok_withLsCodeLoaded_of_plain hVarint)
    (subroutine_ok_withLsCodeLoaded_of_plain hSkip)
    (LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateSubMergesStepsR.e2ar_polyBytesMerge_of_signed hBytes)

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateAuthCountedR
