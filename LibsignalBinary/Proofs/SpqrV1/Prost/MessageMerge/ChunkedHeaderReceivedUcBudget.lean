/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Inner `Unchunked.HeaderReceived` Loop for `Chunked.HeaderReceived::merge` (Block `306`)

Proves the budget-threaded `decode_varint`, `bytes::merge` (`tag = 3`), `skip_field`, and inner
`Unchunked.HeaderReceived` loop induction (`chunkedHeaderReceived_uc_loop_ok_cl_placed`) on Block `306`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length mergeBytes skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeCapOk BytesMergeGhost IsDropSuffix SkipFieldGhost bv32_zeroExtend_ofNat
   decodeVarint_suffix itag_beq_tag_false key_shr32_of_ge key_shr32_of_lt key_wt_none key_wt_some
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join
   sf_truncate32_ofNat64 skip_suffix
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt
   suffix_trans tag_cbz_false w1_tag_eq)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.ProtoRepr
  (headerReceivedPBAt optAuthenticatorPBAt optHeaderReceivedPBAt rustBytesVecAt unchunked3At)
open CryptoVerification.SpqrV1.Auth
  (WppPost optAuthenticatorPBCapAt optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt
   optAuthenticatorPBCapAt_mono setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderReceivedMergeGhost ChunkedInl10CalleeSaved SepWPpLscro
   blkPC_306 blkPl_306 bv64_add_zero bv64_sub_zero cells2_memRegion32_entails_40_160
   chunkedHeaderReceivedMerge_fnOff chunkedHeaderReceivedPBAt
   chunkedInlBelowStack chunkedInlBelow_bytesMerge3 chunkedInlBelow_bytesMerge3_entails
   chunkedInlBelow_decodeVarint2 chunkedInlBelow_decodeVarint2_entails
   chunkedInlBelow_skipField97 chunkedInlBelow_skipField97_entails
   cmp_len_limit_of_gt codecWireTypeToProto
   memRegion_48_cells1_160 memRegion_48_cells2_160
   mergeBytes_length mergeBytes_suffix
   mergeLoopBin mergeLoopBin_eq_limit mergeLoopBin_lt_limit
   mergeLoopBin_of_decodeVarint_none mergeLoopBin_of_key_ge mergeLoopBin_of_key_ok
   mergeLoopBin_of_tag_zero mergeLoopBin_of_wt_none
   protoPrefixStep_unchunked_headerReceived_mergeField proto_mergeMessage_suffix
   unchunked3CapAt unchunked3CapAt_entails_chunkedHeaderReceivedPBAt
   unchunked3CapAt_eq_hr unchunked3CapAt_mono
   unchunkedHeaderReceived_mergeField_other unchunkedHeaderReceived_mergeField_tag1
   unchunkedHeaderReceived_mergeField_tag2 unchunkedHeaderReceived_mergeField_tag3
   vecU8CapAt_hr_mono)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack skipField3Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (BytesMerge3EnvCore FitsEnv.spqrMergeLoop_bytesHead FitsEnv.spqrMergeLoop_split
   SpqrMergeLoopEnv SpqrMergeLoopEnv.bytesSingle SpqrMergeSmallStep
   decodeErrorPushMergeBudgetSpec mergeBytes_len_bound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcBudgetAux
  (chunkedHeaderReceivedErrFrame chunkedHeaderReceivedLoopPre chunkedHeaderReceivedUcLoopPre
   chunkedHeaderReceived_uc_field_push_exit_placed
   chunkedHeaderReceived_uc_from_push_exit_placed
   chunkedHeaderReceived_uc_loop_le_exit_placed
   chunkedHeaderReceived_uc_push_exit_placed
   chunkedHeaderReceived_uc_tag1_wt_err_step_placed
   chunkedHeaderReceived_uc_tag2_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderReceivedMergeEnv chunkedHeaderReceivedMergeSpec headerReceivedPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some
   decodeVarint2Env_to_spqr fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (BytesMerge3Env bytesMerge3RawBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (DecodeVarint2Env decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (SkipField3Env skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderReceivedMerge_fnOff

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem fitsEnv_bytesMerge3_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f₀ f_tot maxLen polyCapBound : Nat} {wt : WireType} {valCap : BitVec 64}
    {bs : List (BitVec 8)} {evs₀ : List AllocEvent}
    (hf : f₀ + max 1 (2 * bs.length) ≤ f_tot) (hbs : bs.length ≤ maxLen)
    (hevs₀ : SpqrMergeLoopEnv f₀ maxLen polyCapBound evs₀)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv f_tot maxLen polyCapBound)) :
    FitsEnv M lim (M.stepEvents evs₀ st) (BytesMerge3EnvCore wt valCap bs) := by
  have hrem : FitsEnv M lim (M.stepEvents evs₀ st)
      (SpqrMergeLoopEnv (max 1 (2 * bs.length)) maxLen polyCapBound) :=
    FitsEnv.spqrMergeLoop_split hevs₀ (hFit.mono fun _ h => h.mono_fuel hf)
  exact FitsEnv.spqrMergeLoop_bytesHead hbs (Nat.le_refl _) hrem

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_306).base

theorem chunkedHeaderReceived_uc_tag1_varint_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          ek { uc with epoch := v } x.bs rest' (headerReceivedPolyCapBound x))
        (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_306).base + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        ek uc x.bs rest (headerReceivedPolyCapBound x))
      (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, receivingEk := ek }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
      (ret_pc := entry + 568#64) hVarintCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hrest_lt (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv hdv
      apply sepWPpLscro_of_vm (mid := entry + 972#64)
      (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv,
        stackAt_decodeVarint2_raw_eq, memRegion_48_cells1_160 s0.sp,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp])
      apply SepWP.exists_elim; intro evs_v; apply SepWP.exists_elim; intro v_stk0
      apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr rest.length ek uc) (by sep_focus)
      apply SepWP.fold
        (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
          (Nat.le_refl (6 * (x.bs.length - rest.length) + 1)) hevs (decodeVarint2Env_to_spqr hevs_v))
        (by sep_focus)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm2 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm2]
      apply sepWPpLscro_of_vm (mid := entry + 988#64)
      by_vm_steps
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hdv, unchunked3CapAt_eq_hr,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecU8CapAt_hr_mono A.repAlloc x.msgPtr uc.hdr hrest'_le) (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest'.length))
            hevs (decodeVarint2Env_eq_nil_of_some hdv hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderReceivedUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            ek { uc with epoch := v } x.bs rest' (headerReceivedPolyCapBound x))
          (by dsimp only [chunkedHeaderReceivedUcLoopPre]; rw [unchunked3CapAt_eq_hr]; simp only [arm64_norm]; sep_entail)
        exact hcont v rest' _ hdv
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
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          ek { uc with hdr := v } x.bs rest' (headerReceivedPolyCapBound x))
        (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_306).base + 392#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        ek uc x.bs rest (headerReceivedPolyCapBound x))
      (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hfpush := @chunkedHeaderReceived_uc_field_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, receivingEk := ek }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 290)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, spqrPoolAt, unchunked3CapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_bytesMerge3 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    apply SepWP.exists_elim; intro cap_hdr
    apply SepWP.exists_elim; intro ptr_hdr
    apply SepWP.exists_elim; intro evs
    wp_focus_pure; intro hevs
    wp_focus_pure; intro hcap_hdr
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    let x_bm : BytesMergeGhost := ⟨iwt, x.msgPtr, cap_hdr, ptr_hdr, uc.hdr, x.bufRef, x.slot, restPtr, rest⟩
    refine call_budget_lscro (x := (x_bm, M.stepEvents evs st))
      (ret_pc := entry + 404#64) hBytesCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [bytesMerge3RawBudgetSpec, x_bm]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20],
        by simp only [arm64_norm, wp_norm, hx19],
        hrest_lt,
        hcap_hdr,
        fitsEnv_bytesMerge3_of_spqr (by dsimp only [x_bm]; omega) hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes iwt rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply sepWPpLscro_of_vm (mid := entry + 856#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm; apply SepWP.exists_elim; intro v_stk0
        wp_focus_pure; intro htrm; wp_focus_pure; intro hevs_bm; wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have hhdr : vecU8At A.repAlloc x.msgPtr cap_hdr ptr_hdr uc.hdr ⊢ rustBytesVecAt A.repAlloc x.msgPtr uc.hdr :=
          Entails.sepExists_right cap_hdr (Entails.sepExists_right ptr_hdr (Entails.refl _))
        apply SepWP.fold hhdr (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_entails_optAuthenticatorPBAt A.repAlloc (x.msgPtr + 0x18#64) rest.length uc.auth) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + 1))
            hevs (SpqrMergeSmallStep.bytesMergeErr iwt cap_hdr rest hmb hevs_bm))
          (by sep_focus)
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 988#64)
        wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame, chunkedHeaderReceivedPBAt,
                optHeaderReceivedPBAt, headerReceivedPBAt, unchunked3At]; sep_entail)
        exact hfpush hFit hnone (by omega) (by decide : 0 ≤ 1) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hmb_len := mergeBytes_len_bound hmb
      have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [bytesMerge3RawBudgetSpec, x_bm, hmb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_bm
        apply SepWP.exists_elim; intro cap_hdr'
        apply SepWP.exists_elim; intro ptr_hdr'
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_bm
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hcap_hdr'
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_bytesMerge3_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        have hhdr_cap : vecU8At A.repAlloc x.msgPtr cap_hdr' ptr_hdr' v ⊢
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest'.length⌝ ∗ vecU8At A.repAlloc x.msgPtr cap ptr v) :=
          Entails.trans (Entails.pure_right hcap_hdr' (Entails.refl _))
            (Entails.sepExists_right cap_hdr' (Entails.sepExists_right ptr_hdr' (Entails.refl _)))
        apply SepWP.fold hhdr_cap (by sep_focus)
        apply SepWP.fold (optAuthenticatorPBCapAt_mono A.repAlloc (x.msgPtr + 0x18#64) uc.auth hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (f₃ := 6 * (x.bs.length - rest'.length)) (by omega)
            hevs (SpqrMergeLoopEnv.bytesSingle (fuel := 0) hmb hrest_le hevs_bm))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderReceivedUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            ek { uc with hdr := v } x.bs rest' (headerReceivedPolyCapBound x))
          (by dsimp only [chunkedHeaderReceivedUcLoopPre, unchunked3CapAt]; sep_entail)
        exact hcont v rest' _ hmb
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
          (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_decode_key_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderReceivedMergeEnv x))
    (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_uc_none :
      mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_306).base + 468#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          ek uc x.bs rest (headerReceivedPolyCapBound x))
        (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_306).base + 416#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        ek uc x.bs cur (headerReceivedPolyCapBound x))
      (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, receivingEk := ek }
  have hfrom_push := @chunkedHeaderReceived_uc_from_push_exit_placed _ M A lim H hFromCall hPushCall x st R s0
    { uc := some uc, receivingEk := ek }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp])
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
      (by dsimp only [decodeVarint2Spec, decodeVarint2SpecGen];
          simp only [sepConj_assoc, A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp, hx19, stackAt_decodeVarint2_raw_eq]; try rfl)
      (And.intro hcur_lt (fitsEnv_decodeVarint2_of_spqr (by omega) hevs hFit))
      (by dsimp only [sliceCursorAt, curPtr]; sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hd : decodeVarint cur with
    | none =>
      have hnone := hnone_of_uc_none
        (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd)
      apply sepWPpLscro_of_vm (mid := entry + 728#64)
      by_vm_steps
        (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
          stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
          sepConj_assoc, arm64_norm, wp_norm, hsp])
        apply SepWP.exists_elim; intro evs_v
        apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr cur.length ek uc) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_snoc A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - cur.length) + 1))
            hevs (decodeVarint2Env_to_spqr hevs_v))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            memRegion (s0.sp - 128#64) 48 ∗
            chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - cur.length) + 1)
              (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm1 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨key, rest⟩
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
      by_cases hk_ge : 2 ^ 32 ≤ key.toNat
      · have hnone := hnone_of_uc_none
          (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge)
        have hshr := key_shr32_of_ge hk_ge
        apply sepWPpLscro_of_vm (mid := entry + 716#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
            stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
            sepConj_assoc, arm64_norm, wp_norm, hsp])
          apply SepWP.exists_elim; intro evs_v
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr cur.length ek uc) (by sep_focus)
          apply SepWP.fold
            (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
              (Nat.le_refl (6 * (x.bs.length - cur.length)))
              hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
            (by sep_focus)
          (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
          (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
          apply SepWP.exists_elim; intro v_err0
          apply SepWP.exists_elim; intro v_err1
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
            rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
          apply SepWP.fold h40 (by sep_focus)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
          rw [← spqrPoolAt_of_vmPreserved hvm2]
          apply SepWPpLscro.weaken_pre
            (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗
              memRegion (s0.sp - 120#64) 40 ∗
              stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
              chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                { uc := some uc, receivingEk := ek } x.bs)
            (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
          exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
             by simp only [arm64_norm, wp_norm, hx28_m],
             by simp only [arm64_norm, wp_norm, hvregs_m]⟩
      · have hshr := key_shr32_of_lt hk_ge
        cases hwt : WireType.ofNat? (key.toNat % 8) with
        | none =>
          have hnone := hnone_of_uc_none
            (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt)
          obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
          apply sepWPpLscro_of_vm (mid := entry + 716#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
              stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
              sepConj_assoc, arm64_norm, wp_norm, hsp])
            apply SepWP.exists_elim; intro evs_v
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
            apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr cur.length ek uc) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - cur.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp])
            (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
            apply SepWP.exists_elim; intro v_err0
            apply SepWP.exists_elim; intro v_err1
            wp_steps
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
            apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
            have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
              rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
            apply SepWP.fold h40 (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗
                memRegion (s0.sp - 120#64) 40 ∗
                stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                  (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                  { uc := some uc, receivingEk := ek } x.bs)
              (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
            exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        | some iwt =>
          obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
          obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
          obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
          by_cases hitag0 : key.toNat / 8 < 1
          · have hnone := hnone_of_uc_none
              (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_headerReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
            have htag_zero : key.toNat / 8 = 0 := by omega
            apply sepWPpLscro_of_vm (mid := entry + 716#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr cur.length ek uc) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (Nat.le_refl (6 * (x.bs.length - cur.length)))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              (conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp])
              (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
              apply SepWP.exists_elim; intro v_err0
              wp_steps
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
              apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗
                  memRegion (s0.sp - 120#64) 40 ∗
                  stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
                  chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - cur.length))
                    (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                    { uc := some uc, receivingEk := ek } x.bs)
                (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
              exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
                (by simp only [arm64_norm, wp_norm])
                (by simp only [arm64_norm, wp_norm, hrunm])
                (by simp only [arm64_norm, wp_norm, hspm])
                (by simp only [arm64_norm, wp_norm, htrm, htr])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩
          · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
            have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
              rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
              simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
            apply sepWPpLscro_of_vm (mid := entry + 468#64)
            by_vm_steps
              (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen, hd,
                stackAt_decodeVarint2_raw_eq, sepExists_sepConj_left, sepExists_sepConj_right,
                sepConj_assoc, arm64_norm, wp_norm, hsp])
              apply SepWP.exists_elim; intro evs_v
              apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_v⟩, hsm0, hsm1⟩
              apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
              apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
              apply SepWP.fold (unchunked3CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth uc.hdr hrest_le_cur) (by sep_focus)
              apply SepWP.fold
                (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                  (by omega : 6 * (x.bs.length - cur.length) ≤ 6 * (x.bs.length - rest.length))
                  hevs (decodeVarint2Env_eq_nil_of_some hd hevs_v))
                (by sep_focus)
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
              rw [← spqrPoolAt_of_vmPreserved hvm2]
              apply SepWPpLscro.weaken_pre
                (P' := chunkedHeaderReceivedUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                  ek uc x.bs rest (headerReceivedPolyCapBound x))
                (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
              exact hcont key iwt rest _ hd hk_ge hwt hitag0
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
                (by simp only [arm64_norm, wp_norm, hx26_m])
                ⟨by simp only [arm64_norm, wp_norm, hx27_m],
                 by simp only [arm64_norm, wp_norm, hx28_m],
                 by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hSkipCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {ek : Option PolynomialDecoder} {uc : V1State.Unchunked.HeaderReceived}
    {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderReceived.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_306).base + 416#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderReceivedUcLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          ek uc x.bs rest' (headerReceivedPolyCapBound x))
        (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_306).base + 492#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
      (chunkedHeaderReceivedUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
        ek uc x.bs rest (headerReceivedPolyCapBound x))
      (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩
  have hpush_exit := @chunkedHeaderReceived_uc_push_exit_placed _ M A lim H hPushCall x st R s0
    { uc := some uc, receivingEk := ek }
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderReceivedUcLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField97 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 504#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt],
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
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
    | none =>
      have hnone := hnone_of_sf hsf
      apply sepWPpLscro_of_vm (mid := entry + 728#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_entails_chunkedHeaderReceivedPBAt A.repAlloc x.msgPtr rest.length ek uc) (by sep_focus)
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
            chunkedHeaderReceivedErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerReceivedPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { uc := some uc, receivingEk := ek } x.bs)
          (by dsimp only [chunkedHeaderReceivedErrFrame]; sep_entail)
        exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some rest' =>
      have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
      apply sepWPpLscro_of_vm (mid := entry + 416#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedInlBelow_skipField97_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (unchunked3CapAt_mono A.repAlloc x.msgPtr uc.epoch uc.auth uc.hdr hrest'_le) (by sep_focus)
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
          (P' := chunkedHeaderReceivedUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            ek uc x.bs rest' (headerReceivedPolyCapBound x))
          (by dsimp only [chunkedHeaderReceivedUcLoopPre]; sep_entail)
        exact hcont rest' _ hsf
          (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm]) (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m]) (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m]) (by simp only [arm64_norm, wp_norm, hx22_m])
          (by simp only [arm64_norm, wp_norm, hx23_m]) (by simp only [arm64_norm, wp_norm, hx24_m])
          (by simp only [arm64_norm, wp_norm, hx25_m]) (by simp only [arm64_norm, wp_norm, hx26_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m], by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderReceived_uc_loop_ok_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)))
    (hPushCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hVarintCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)))
    (hSkipCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    (hAuthCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)))
    (hBytesCall : subroutine_ok ((blkPC_306).rebase (blkPl_306).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)))
    {x : ChunkedHeaderReceivedMergeGhost} {st : M.σ} {R : SepProp} {s0 : State}
    {ek : Option PolynomialDecoder} {outerLimit innerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderReceivedMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.HeaderReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.HeaderReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_306).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
        s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
        s'.readReg64 (Reg.gpr 25#5) = 8#64 → ChunkedInl10CalleeSaved s0 s' →
        SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s'
          (chunkedHeaderReceivedLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
            { uc := some uc', receivingEk := ek } x.bs rest' (headerReceivedPolyCapBound x))
          (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R)) →
      (mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (mergeMessage V1State.Chunked.HeaderReceived.mergeField
          (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_306).base + 416#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_306).rebase (blkPl_306).base H) (s0.readReg64 Reg.lr) s
        (chunkedHeaderReceivedUcLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr
          ek uc x.bs cur (headerReceivedPolyCapBound x))
        (WppPost (chunkedHeaderReceivedMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have htag1_varint := fun {s uc rest} =>
    @chunkedHeaderReceived_uc_tag1_varint_step_cl_placed _ M A lim H hPushCall hVarintCall x st R s0 s ek uc rest outerLimit innerLimit hFit
  have htag1_wt_err := fun {s uc rest iwt} =>
    @chunkedHeaderReceived_uc_tag1_wt_err_step_placed _ M A lim H hFromCall hPushCall x st R s0 s ek uc rest iwt hFit
  have htag2_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderReceived_uc_tag2_step_placed _ M A lim H hPushCall hAuthCall x st R s0 s ek uc rest iwt outerLimit innerLimit hFit
  have htag3_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedHeaderReceived_uc_tag3_step_cl_placed _ M A lim H hPushCall hBytesCall x st R s0 s ek uc rest iwt outerLimit innerLimit hFit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) =>
    @chunkedHeaderReceived_uc_skip_step_cl_placed _ M A lim H hPushCall hSkipCall x st R s0 s ek uc rest iwt tag outerLimit innerLimit hFit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall hFit (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
      (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hok_cont hnone_cont hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedHeaderReceived_uc_loop_le_exit_placed hFromCall hPushCall hFit hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_cont (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt))
        (fun s' heq => hok_cont uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedHeaderReceived_uc_decode_key_step_cl_placed hFromCall hPushCall hVarintCall hFit hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_cont ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97)
        protoPrefixStep_unchunked_headerReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag1] at hstep
        by_cases hiwt : iwt = .varint
        · subst hiwt
          apply sepWPpLscro_of_vm (mid := entry + 556#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderReceivedUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderReceivedUcLoopPre]
            refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf
              (fun hdv => hnone_cont (by simp [hstep, hdv]))
              (fun v rest' s'' hdv hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0', WireType.toNat]) (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
              (by simp only [arm64_norm, wp_norm, hx24']) (by simp only [arm64_norm, wp_norm, hx25'])
              (by simp only [arm64_norm, wp_norm, hx26'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'], by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
            have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv
            have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
            have hstep1 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with epoch := v } rest' innerLimit 97 := by simp [hstep, hdv]
            exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv))
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep1.trans hml))
              (fun hml => hnone_cont (hstep1.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · apply sepWPpLscro_of_vm (mid := entry + 556#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderReceivedUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderReceivedUcLoopPre]
            exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_cont (by simp [hstep, hiwt]))
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'], by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag2] at hstep
          apply sepWPpLscro_of_vm (mid := entry + 512#64)
          by_vm_steps
            wp_steps
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
            rw [chunkedHeaderReceivedUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderReceivedUcLoopPre]
            refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf
              (fun hauth => hnone_cont (by simp [hstep, hauth]))
              (fun auth' rest' s'' hauth hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
              (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
              (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
              (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
              (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
              (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
              (by simp only [arm64_norm, wp_norm, hx24']) (by simp only [arm64_norm, wp_norm, hx25'])
              (by simp only [arm64_norm, wp_norm, hx26'])
              ⟨by simp only [arm64_norm, wp_norm, hx27'], by simp only [arm64_norm, wp_norm, hx28'],
               by simp only [arm64_norm, wp_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth).1
            have hstep2 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with auth := some auth' } rest' innerLimit 97 := by simp [hstep, hauth]
            exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth).2)
              (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep2.trans hml))
              (fun hml => hnone_cont (hstep2.trans hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedHeaderReceived_mergeField_tag3] at hstep
            apply sepWPpLscro_of_vm (mid := entry + 392#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
              rw [chunkedHeaderReceivedUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderReceivedUcLoopPre]
              refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf
                (fun hmb => hnone_cont (by simp [hstep, hmb]))
                (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx19'])
                (by simp only [arm64_norm, wp_norm, hx20']) (by simp only [arm64_norm, wp_norm, hx21'])
                (by simp only [arm64_norm, wp_norm, hx22']) (by simp only [arm64_norm, wp_norm, hx23'])
                (by simp only [arm64_norm, wp_norm, hx24']) (by simp only [arm64_norm, wp_norm, hx25'])
                (by simp only [arm64_norm, wp_norm, hx26'])
                ⟨by simp only [arm64_norm, wp_norm, hx27'], by simp only [arm64_norm, wp_norm, hx28'],
                 by simp only [arm64_norm, wp_norm, hvregs']⟩
              have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
              have hstep3 : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                  mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) { uc with hdr := v } rest' innerLimit 97 := by simp [hstep, hmb]
              exact ih { uc with hdr := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
                (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb))
                (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep3.trans hml))
                (fun hml => hnone_cont (hstep3.trans hml))
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
            obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
            obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32)
            have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
            have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
            have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
            have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
            have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
            have hb3_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 3#32) = true := by simp only [bne, hb3_1, Bool.not_false]
            have hb3_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 3#32) = true := by simp only [bne, hb3_2, Bool.not_false]
            rw [unchunkedHeaderReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3] at hstep
            apply sepWPpLscro_of_vm (mid := entry + 492#64)
            by_vm_steps
              wp_steps
              apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              refine ⟨by simp only [arm64_norm, wp_norm], fun hvm_d => ?_⟩
              rw [chunkedHeaderReceivedUcLoopPre, ← spqrPoolAt_of_vmPreserved hvm_d, ← chunkedHeaderReceivedUcLoopPre]
              refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
                (fun hsf => hnone_cont (by simp [hstep, hsf]))
                (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
                (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun'])
                (by simp only [arm64_norm, wp_norm, hsp']) (by simp only [arm64_norm, wp_norm, htr'])
                (by simp only [arm64_norm, wp_norm, hx0']) (by simp only [arm64_norm, wp_norm, hx1', sf_truncate32_ofNat64])
                (by simp only [arm64_norm, wp_norm, hx19']) (by simp only [arm64_norm, wp_norm, hx20'])
                (by simp only [arm64_norm, wp_norm, hx21']) (by simp only [arm64_norm, wp_norm, hx22'])
                (by simp only [arm64_norm, wp_norm, hx23']) (by simp only [arm64_norm, wp_norm, hx24'])
                (by simp only [arm64_norm, wp_norm, hx25']) (by simp only [arm64_norm, wp_norm, hx26'])
                ⟨by simp only [arm64_norm, wp_norm, hx27'], by simp only [arm64_norm, wp_norm, hx28'],
                 by simp only [arm64_norm, wp_norm, hvregs']⟩
              have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
              have hstep_other : mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 =
                  mergeLoopBin V1State.Unchunked.HeaderReceived.mergeField (rest'.length - innerLimit) uc rest' innerLimit 97 := by simp [hstep, hsf]
              exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
                (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
                (fun uc' r'' s3 heq hr''_le hr''_suf hml => hok_cont uc' r'' s3 heq hr''_le hr''_suf (hstep_other.trans hml))
                (fun hml => hnone_cont (hstep_other.trans hml))
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceivedUcBudget
