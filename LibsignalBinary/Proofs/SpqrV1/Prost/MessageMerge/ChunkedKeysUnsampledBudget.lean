/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledUcBudget
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
# Budget-Threaded Verification of `Chunked.KeysUnsampled::merge` (Block `305`)

Proves the budget-threaded outer loop induction and top-level contract
`chunked_keys_unsampled_merge_cl_placed_ok_of_contracts` against
`withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)` on Block `305`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix SkipFieldGhost decodeVarint_suffix
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   skip_suffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans ule_len_of_ge ule_len_of_lt)
open CryptoVerification.LibsignalTripleRatchet.Prost.BytesMergeFacts
  (truncate32_zeroExtend64_and_255_eq)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedKeysUnsampledMergeGhost PolyCalleeSaved SepWPpLscro
   bv64_add_zero bv64_sub_zero bv_len_sub_limit chunkedInlBelowStack
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails chunkedInlBelow_skipField98
   chunkedInlBelow_skipField98_entails chunkedKeysUnsampledMerge_fnOff
   chunkedKeysUnsampledPBCapAt_entails_pb chunkedKeysUnsampledPBCapAt_mono
   chunkedKeysUnsampled_mergeField_other chunkedKeysUnsampled_mergeField_tag1
   codecWireTypeToProto memRegion_48_cells1_160 memRegion_48_wtErr160 mergeLoopBin
   mergeLoopBin_eq_limit mergeLoopBin_lt_limit mergeLoopBin_of_key_ok mergeMessageBin
   mergeMessageBin_eq_proto_mergeMessage polySavedRegs polySavedRegs_entails_any
   protoPrefixStep_chunked_keysUnsampled_mergeField
   protoPrefixStep_unchunked_keysUnsampled_mergeField proto_mergeMessage_suffix
   stackAt_chunkedInl_prologue subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
   unchunked2CapAt_entails_chunkedKeysUnsampledPBAt unchunked2CapAt_mono withLscroProp
   wtErr160_entails_memRegion40 wt_beq_two_of_lengthDelimited
   wt_beq_two_of_ne_lengthDelimited)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_305 blkPl_305)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (SpqrMergeIterEnv SpqrMergeLoopEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedKeysUnsampledMergeEnv chunkedKeysUnsampledMergeSpec chunkedKeysUnsampledMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledBudgetAux
  (chunkedKeysUnsampled_decode_key_step_cl_placed chunkedKeysUnsampled_dispatch_step_placed
   chunkedKeysUnsampled_loop_le_exit_cl_placed chunkedKeysUnsampled_uc_init_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledUcBudget
  (chunkedKeysUnsampled_uc_loop_ok_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledUcBudgetAux
  (chunkedKeysUnsampledErrFrame chunkedKeysUnsampledLoopPre chunkedKeysUnsampledUcLoopPre
   chunkedKeysUnsampled_from_err_exit_placed chunkedKeysUnsampled_ret_err_exit_placed
   chunkedKeysUnsampled_uc_from_push_exit_placed chunkedKeysUnsampled_uc_push_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr pool_entails_spqrPoolAt_nil
   pool_entails_spqrPoolAt_snoc sepWPpLscro_of_vm sepWPpLscro_pure_elim
   skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr spqrPoolAt spqrPoolAt_of_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedKeysUnsampledMerge_fnOff

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

private theorem iwt64_beq_two_of_ne_ld {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> simp_all [WireType.toNat]

private theorem setWidth8_zext64_trunc32_ofNat64_wt (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) =
      BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_305).base

theorem chunkedKeysUnsampled_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysUnsampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩
  have hret_err := @chunkedKeysUnsampled_ret_err_exit_placed _ M A lim H x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [chunkedKeysUnsampledLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField98 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 184#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx8, setWidth8_zext64_trunc32_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx1],
        htag_lt,
        by simp only [arm64_norm, wp_norm, hx19],
        by simp only [arm64_norm, wp_norm],
        by decide,
        hrest_lt,
        fitsEnv_skipField_of_spqr (by omega) hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
    | none =>
      have hnone := hnone_of_skip hsf
      apply sepWPpLscro_of_vm (mid := entry + 128#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A.repAlloc x.msgPtr rest.length m) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (skipFieldEnv_to_spqr hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            memRegion (s0.sp - 128#64) 48 ∗
            chunkedKeysUnsampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := entry + 188#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest'.length))
            hevs (skipFieldEnv_eq_nil_of_some hsf hevs_sf))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedKeysUnsampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
          (by dsimp only [chunkedKeysUnsampledLoopPre]; sep_entail)
        exact hcont rest' _ hsf
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
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedKeysUnsampled_tag1_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysUnsampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (mergeMessage V1State.Unchunked.KeysUnsampled.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.KeysUnsampled) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage V1State.Unchunked.KeysUnsampled.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr { uc := some uc' } x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_305).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  refine chunkedKeysUnsampled_uc_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1
  rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1
  obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let uc0 : V1State.Unchunked.KeysUnsampled := m.uc.getD default
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedKeysUnsampled_uc_push_exit_placed _ M A lim H hPushCall x st R s0 { uc := some uc0 }
  have hfrom_push := @chunkedKeysUnsampled_uc_from_push_exit_placed _ M A lim H hFromCall hPushCall x st R s0 { uc := some uc0 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_uc_loop_ok_cl_placed _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall
      x st R s0 outerLimit innerLimit hFit hsp_align hbs_lt hlim_lt
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, spqrPoolAt,
        sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
        (ret_pc := entry + 292#64) hVarintCall
        (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
        (by simp only [arm64_norm, wp_norm])
        (by conv =>
              lhs
              dsimp only [decodeVarint2Spec, decodeVarint2SpecGen]
              simp only [sepConj_assoc]
              arg 2
              simp only [A.pool_of_vmPreserved hvm1, stackAt_decodeVarint2_raw_eq, arm64_norm, wp_norm, hsp1])
        (by exact ⟨by simp only [arm64_norm, wp_norm, hx19_1],
          hrest_lt,
          fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit⟩)
        (by sep_focus) ?_
      intro sm hpcm hrunm hspm hcsm
      simp only [CalleeSavedPreserved] at hcsm
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint rest with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 616#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A.repAlloc x.msgPtr rest.length uc0) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
              hevs (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              memRegion (s0.sp - 128#64) 48 ∗
              chunkedKeysUnsampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
                s0 _ x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
            (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
          exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm1 hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr1])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx26_m],
             by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      | some p =>
        rcases p with ⟨len, rest0⟩
        have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
        have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
        have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
        have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
        have hrest0_suf : IsDropSuffix x.bs rest0 :=
          suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
        let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
        by_cases hlt_len : rest0.length < len.toNat
        · have hule := ule_len_of_lt hlt_len hrest0_lt
          have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            apply hnone_of_uc
            rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint rest with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 604#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, memRegion_48_cells1_160 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
            apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A.repAlloc x.msgPtr rest.length uc0) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - rest.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
            (conv => arg 4; simp only [sepConj_assoc])
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
                chunkedKeysUnsampledErrFrame A lim st (6 * (x.bs.length - rest.length))
                  s0 _ x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
              (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
            exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hres0 : (mergeMessage V1State.Unchunked.KeysUnsampled.mergeField
              (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
              (mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
                (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint rest with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
                conv_rhs => rw [hrest0_suf, List.drop_drop]
                congr 1; omega
              simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                hdv0_p, Except.toOption, hlt_len, hdrop_eq]
              rcases mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 344#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
              sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
            apply SepWP.fold (unchunked2CapAt_mono A.repAlloc x.msgPtr uc0.epoch uc0.auth hrest0_le_rest) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest0.length))
                hevs (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt])
            (conv => arg 4; simp only [sepConj_assoc])
            wp_steps
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := chunkedKeysUnsampledUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr uc0 x.bs rest0)
              (by dsimp only [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter]; sep_entail)
            exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf
              (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f => by
                have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
                refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f
                rw [hres0, hml, hr'_eq]; rfl)
              (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
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
              (by simp only [arm64_norm, wp_norm, hsm1, hsub])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply sepWPpLscro_of_vm (mid := entry + 604#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
        sliceCursorAt, memRegion_48_wtErr160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro b_wt1
      apply SepWP.exists_elim; intro b_wt0
      apply SepWP.exists_elim; intro v_wt0
      wp_steps
      apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A.repAlloc x.msgPtr rest.length uc0) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedKeysUnsampledErrFrame A lim st (6 * (x.bs.length - rest.length))
            s0 _ x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; rw [spqrPoolAt_of_vmPreserved hvm1]; sep_entail)
      exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [arm64_norm, wp_norm, hsp1])
        (by simp only [arm64_norm, wp_norm, htr1])
        ⟨by simp only [arm64_norm, wp_norm, hx26_1],
         by simp only [arm64_norm, wp_norm, hx27_1],
         by simp only [arm64_norm, wp_norm, hx28_1],
         by simp only [arm64_norm, wp_norm, hvregs_1]⟩

theorem chunkedKeysUnsampled_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    {x : ChunkedKeysUnsampledMergeGhost} {st : M.σ} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedKeysUnsampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.KeysUnsampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField
          (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_305).base + 188#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
        (chunkedKeysUnsampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    exact chunkedKeysUnsampled_loop_le_exit_cl_placed hFromCall hFit (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedKeysUnsampled_loop_le_exit_cl_placed hFromCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedKeysUnsampled_decode_key_step_cl_placed hFromCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98)
        protoPrefixStep_chunked_keysUnsampled_mergeField hle_lim hd hk_ge hwt hitag0
      refine chunkedKeysUnsampled_dispatch_step_placed htag_lt ?_ ?_
        hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      · intro htag1 s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        rw [htag1, chunkedKeysUnsampled_mergeField_tag1] at hloop_ok
        refine chunkedKeysUnsampled_tag1_step_cl_placed hFromCall hPushCall hVarintCall hSkipCall hAuthCall
          hFit hsp_align hbs_lt hrest_le hrest_lt hrest_suf
          (fun huc => by rw [hres, hloop_ok, huc]; rfl)
          (fun uc' rest' s'' huc hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        have hucf := proto_mergeMessage_suffix huc
        exact ih { uc := some uc' } rest' s'' (by have := hucf.1; omega) (by have := hucf.1; omega)
          (suffix_trans hrest_le hrest_suf hucf.1 hucf.2)
          (by rw [hres, hloop_ok, huc]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs''
      · intro hne1 s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        rw [chunkedKeysUnsampled_mergeField_other m iwt rest 98 htag_lt hne1] at hloop_ok
        refine chunkedKeysUnsampled_skip_step_cl_placed hSkipCall hFit hsp_align hrest_le hrest_lt hrest_suf htag_lt
          (fun hsf => by rw [hres, hloop_ok, hsf]; rfl)
          (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
        exact ih m rest' s'' (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
          (by rw [hres, hloop_ok, hsf]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs''

theorem chunked_keys_unsampled_merge_cl_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim))) :
    subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (blkPl_305).base
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A lim)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedKeysUnsampledMergeSpec chunkedKeysUnsampledMergeSpecOfEnv
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp_align
  replace hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine ⟨_, hpre, ?_⟩
  dsimp only
  apply CryptoVerification.SpqrV1.Prost.MessageMerge.SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedKeysUnsampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)
  apply sepWPpLscro_pure_elim
  rintro ⟨h_1, h_2, h_3, hbs_lt, hFit⟩
  have hret_err := @chunkedKeysUnsampled_ret_err_exit_placed _ M A lim H x st R s0 x.msg
  have hfrom_err := @chunkedKeysUnsampled_from_err_exit_placed _ M A lim H hFromCall x st R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_loop_ok_cl_placed _ M A lim H hFromCall hPushCall hVarintCall hSkipCall hAuthCall
      x st R s0 outerLimit hFit hsp_align hbs_lt hlim_lt
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
      apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
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
      obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, h_2, h_3]
        at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint x.bs with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 128#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_snoc0 A lim st sm (decodeVarint2Env_to_spqr hevs_dv))
            (by sep_focus)
          wp_steps
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              memRegion (s0.sp - 128#64) 48 ∗
              chunkedKeysUnsampledErrFrame A lim st 1 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
            (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
          exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm1 hsp_align
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
          have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 120#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, memRegion_48_cells1_160 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm 0 x.bs.length 0
                (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
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
                chunkedKeysUnsampledErrFrame A lim st 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
              (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
            exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hres0 : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
              (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
                (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
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
              rcases mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField
                (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 188#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
              sliceCursorAt, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A.repAlloc x.msgPtr x.msg hrest0_le) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil0 A lim st sm (6 * (x.bs.length - rest0.length))
                x.bs.length 0 (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            wp_steps
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := chunkedKeysUnsampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
              (by dsimp only [chunkedKeysUnsampledLoopPre, sliceCursorAfter]; sep_entail)
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
              (by simp only [arm64_norm, wp_norm])
              ⟨by simp only [arm64_norm, wp_norm, hx26_m],
               by simp only [arm64_norm, wp_norm, hx27_m],
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
    have hnone : (mergeMessage V1State.Chunked.KeysUnsampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply sepWPpLscro_of_vm (mid := entry + 120#64)
    by_vm_steps
      (conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
      apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
      apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
      apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
      apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
      apply SepWP.fold
        (pool_entails_spqrPoolAt_init A lim st s0 x.bs.length 0)
        (by sep_focus)
      wp_steps
      apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
      apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A.repAlloc x.msgPtr x.bs.length x.msg) (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedKeysUnsampledErrFrame A lim st 0 s0 _ x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hfrom_err hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun])
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm])
        ⟨by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm],
         by simp only [arm64_norm, wp_norm]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledBudget
