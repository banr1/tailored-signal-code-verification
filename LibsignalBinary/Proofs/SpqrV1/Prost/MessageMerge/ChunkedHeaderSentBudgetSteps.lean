/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
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
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Budget-Threaded Outer Tag/Skip Step Proofs for `Chunked.HeaderSent::merge` (Block `302`)

Proves the budget-threaded outer `skip`, `tag = 2` (`sendingEk`), `tag = 3` (`receivingCt1`), and
`tag = 1` (`uc`) step lemmas for `Chunked.HeaderSent::merge` on Block `302`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetSteps

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarint_length skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix SkipFieldGhost decodeVarint_suffix
   pointsTo64_pair_entails_memRegion16 pointsToBytes_prefix_join sliceCursorAfter
   sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt suffix_trans ule_len_of_ge
   ule_len_of_lt)
open CryptoVerification.SpqrV1.Prost.BytesMerge (proto_decodeVarint_toOption)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost setWidth8_ofNat64_wt)
open CryptoVerification.SpqrV1.ProtoRepr (chunkedHeaderSentPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedHeaderSentMergeGhost ChunkedInl10CalleeSaved OptPolyDecoderBound OptPolyEncoderBound
   PolyDecoderMergeGhost PolyEncoderMergeGhost SepWPpLscro
   blkPC_302 blkPl_302 bv64_add_zero bv64_sub_zero bv_len_sub_limit
   chunkedHeaderSentMerge_fnOff chunkedHeaderSentPBCapAt
   chunkedHeaderSentPBCapAt_entails_pb chunkedHeaderSentPBCapAt_mono
   chunkedInlBelowStack chunkedInlBelow_decodeVarint2
   chunkedInlBelow_decodeVarint2_entails chunkedInlBelow_eq_polyMerge
   chunkedInlBelow_skipField98 chunkedInlBelow_skipField98_entails
   codecWireTypeToProto memRegion_48_cells1_160 memRegion_48_wtErr160
   mergeLoopBin mergeMessageBin mergeMessageBin_eq_proto_mergeMessage
   optEkSentPBCapAt_entails optEkSentPBCapAt_mono
   optPolynomialDecoderPBAt_some_eq optPolynomialEncoderPBAt_some_eq
   protoPrefixStep_unchunked_ekSent_mergeField proto_mergeMessage_suffix
   unchunked3CapAt_entails_chunkedHeaderSentPBAt unchunked3CapAt_mono
   wtErr160_entails_memRegion40)
open CryptoVerification.SpqrV1.Varint (decodeVarint2Stack)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (FitsEnv.spqrMergeLoop_split SpqrMergeLoopEnv decodeErrorPushMergeBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedInlinedCommonBudget
  (ChunkedHeaderSentMergeEnv chunkedHeaderSentMergeSpec headerSentPolyCapBound)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro decodeVarint2Env_eq_nil_of_some decodeVarint2Env_to_spqr
   fitsEnv_decodeVarint2_of_spqr fitsEnv_skipField_of_spqr pool_entails_spqrPoolAt_append
   pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc sepWPpLscro_of_vm
   skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr spqrPoolAt spqrPoolAt_of_vmPreserved
   vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetAux
  (chunkedHeaderSent_ct1_init_placed chunkedHeaderSent_ek_init_placed
   chunkedHeaderSent_uc_init_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcClPlacedBudget
  (chunkedHeaderSent_push_ret_exit_cl_placed
   chunkedHeaderSent_uc_from_push_exit_cl_placed chunkedHeaderSent_uc_loop_ok_cl_placed
   chunkedHeaderSent_uc_push_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentUcBudgetAux
  (chunkedHeaderSentErrFrame chunkedHeaderSentLoopPre
   chunkedHeaderSentUcLoopPre chunkedHeaderSent_ret_err_exit_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyDecoderMergePostEnv PolyEncoderMergeEnv PolyEncoderMergePostEnv
   bytesMerge3RawBudgetSpec polyDecoderCapBound polyDecoderMergeSpec polyDecoderMergeSpecOfEnv
   polyEncoderCapBound polyEncoderMergeSpec polyEncoderMergeSpecOfEnv polyMergeLoopEnv_to_spqr)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecGen)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedHeaderSentMerge_fnOff

private theorem setWidth8_zext64_trunc32_ofNat64_wt (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

private theorem iwt64_beq_two_of_ne_ld {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> simp_all [WireType.toNat]

private theorem stackAt_decodeVarint2_raw_eq (sp : BitVec 64) :
    stackAt sp (0x40 + (0x40 + decodeErrorHookStack)) = stackAt sp decodeVarint2Stack := rfl

private theorem fitsEnv_polyEncoderMerge_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f F maxLen polyBound : Nat} {x_poly : PolyEncoderMergeGhost} {evs : List AllocEvent}
    (hf : f + (2 * x_poly.bs.length + 2) ≤ F)
    (hlen : x_poly.bs.length ≤ maxLen)
    (hpoly : polyEncoderCapBound x_poly ≤ polyBound)
    (hevs : SpqrMergeLoopEnv f maxLen polyBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv F maxLen polyBound)) :
    FitsEnv M lim (M.stepEvents evs st) (PolyEncoderMergeEnv x_poly) := by
  have hrem := FitsEnv.spqrMergeLoop_split (f₂ := 2 * x_poly.bs.length + 2) hevs
    (hFit.mono fun _ h => h.mono_fuel hf)
  exact fun evs' hp => hrem evs' (polyMergeLoopEnv_to_spqr hlen hpoly hp)

private theorem fitsEnv_polyDecoderMerge_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f F maxLen polyBound : Nat} {x_poly : PolyDecoderMergeGhost} {evs : List AllocEvent}
    (hf : f + (2 * x_poly.bs.length + 2) ≤ F)
    (hlen : x_poly.bs.length ≤ maxLen)
    (hpoly : polyDecoderCapBound x_poly ≤ polyBound)
    (hevs : SpqrMergeLoopEnv f maxLen polyBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv F maxLen polyBound)) :
    FitsEnv M lim (M.stepEvents evs st) (PolyDecoderMergeEnv x_poly) := by
  have hrem := FitsEnv.spqrMergeLoop_split (f₂ := 2 * x_poly.bs.length + 2) hevs
    (hFit.mono fun _ h => h.mono_fuel hf)
  exact fun evs' hp => hrem evs' (polyMergeLoopEnv_to_spqr hlen hpoly hp)

section ClPlaced

set_option quotPrecheck false in
local notation "entry" => (blkPl_302).base

theorem chunkedHeaderSent_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
          (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 400#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
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
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩
  have hret_err := @chunkedHeaderSent_ret_err_exit_placed _ M A lim H x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [chunkedHeaderSentLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField98 s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_sf, M.stepEvents evs st))
      (ret_pc := entry + 412#64) hSkipCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [skipField3Spec, x_sf]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0, setWidth8_ofNat64_wt, setWidth8_zext64_trunc32_ofNat64_wt],
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
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
    | none =>
      have hnone := hnone_of_skip hsf
      apply sepWPpLscro_of_vm (mid := entry + 124#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (chunkedHeaderSentPBCapAt_entails_pb A.repAlloc x.msgPtr rest.length m) (by sep_focus)
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
            chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
        exact hret_err hnone (by omega) (by decide : 0 ≤ 3) hsm0 hsp_align
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
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
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
        apply SepWP.fold (chunkedHeaderSentPBCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
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
          (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
            (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentLoopPre]; sep_entail)
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
          (by simp only [arm64_norm, wp_norm, hx25_m])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hPolyEncCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hbound : OptPolyEncoderBound m.sendingEk rest.length)
    (hcap_bound : Nat.max (m.sendingEk.getD default).pts.length (m.sendingEk.getD default).polys.length +
      rest.length ≤ headerSentPolyCapBound x)
    (hnone_of_poly :
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingEk := some d' } x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
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
  have hpush_ret := fun {d' : PolynomialEncoder} =>
    @chunkedHeaderSent_push_ret_exit_cl_placed _ M A lim H hPushCall x st R s0
      { m with sendingEk := some d' }
  refine chunkedHeaderSent_ek_init_placed ?_ hpc hrun hsp hx20 hx25 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyEncoderMergeGhost := ⟨iwt, x.msgPtr + 80#64, m.sendingEk.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpoly_cap : polyEncoderCapBound x_poly ≤ headerSentPolyCapBound x := hcap_bound
  apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_eq_polyMerge s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
      (ret_pc := entry + 332#64) hPolyEncCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv, x_poly]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt, setWidth8_zext64_trunc32_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        hbound.1,
        hbound.2,
        fitsEnv_polyEncoderMerge_of_spqr (x_poly := x_poly) (by dsimp only [x_poly]; omega)
          hrest_le hpoly_cap hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hpoly_res : (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingEk.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_poly hpoly_res
      apply sepWPpLscro_of_vm (mid := entry + 904#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_poly, hpoly_res, memRegion_48_cells1_160 s0.sp,
          ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.exists_elim; intro d'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (optEkSentPBCapAt_entails A.repAlloc x.msgPtr rest.length m.uc) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (2 * rest.length + 2)))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 824#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderSentErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (2 * rest.length + 2))
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with sendingEk := some d' } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt];
              rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
        exact hpush_ret hFit hnone (by omega) (by omega : n_err ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨d', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optEkSentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) + 2 * (rest.length - rest'.length) ≤
              6 * (x.bs.length - rest'.length))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with sendingEk := some d' } x.bs rest' (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt];
              rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
        exact hcont d' rest' _ hpoly_res
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
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    (hPolyDecCall : subroutine_ok ((blkPC_302).rebase (blkPl_302).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hbound : OptPolyDecoderBound m.receivingCt1 rest.length)
    (hcap_bound : (m.receivingCt1.getD default).pts.length + rest.length ≤ headerSentPolyCapBound x)
    (hnone_of_poly :
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingCt1.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingCt1.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with receivingCt1 := some d' } x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 244#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
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
  have hpush_ret := fun {d' : PolynomialDecoder} =>
    @chunkedHeaderSent_push_ret_exit_cl_placed _ M A lim H hPushCall x st R s0
      { m with receivingCt1 := some d' }
  refine chunkedHeaderSent_ct1_init_placed ?_ hpc hrun hsp hx20 hx25 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyDecoderMergeGhost := ⟨iwt, x.msgPtr + 136#64, m.receivingCt1.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpoly_cap : polyDecoderCapBound x_poly ≤ headerSentPolyCapBound x := hcap_bound
  apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_eq_polyMerge s0.sp])
    (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
    apply SepWP.exists_elim; intro evs
    apply SepWP.pure_elim; intro hevs
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
      (ret_pc := entry + 280#64) hPolyDecCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv, x_poly]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1, setWidth8_ofNat64_wt, setWidth8_zext64_trunc32_ofNat64_wt],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        hbound,
        fitsEnv_polyDecoderMerge_of_spqr (x_poly := x_poly) (by dsimp only [x_poly]; omega)
          hrest_le hpoly_cap hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hpoly_res : (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingCt1.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_poly hpoly_res
      apply sepWPpLscro_of_vm (mid := entry + 868#64)
      by_vm_steps
        (conv => arg 4; simp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv,
          PolyDecoderMergePostEnv, x_poly, hpoly_res, memRegion_48_cells1_160 s0.sp,
          ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.exists_elim; intro d'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (optEkSentPBCapAt_entails A.repAlloc x.msgPtr rest.length m.uc) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (2 * rest.length + 2)))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 824#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗
            stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
            chunkedHeaderSentErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (2 * rest.length + 2))
              (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with receivingCt1 := some d' } x.bs)
          (by dsimp only [chunkedHeaderSentErrFrame, chunkedHeaderSentPBAt];
              rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
        exact hpush_ret hFit hnone (by omega) (by omega : n_err ≤ 2) hsm0 hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨d', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1
      apply sepWPpLscro_of_vm (mid := entry + 168#64)
      by_vm_steps
        (conv => arg 4; simp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv,
          PolyDecoderMergePostEnv, x_poly, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optEkSentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) + 2 * (rest.length - rest'.length) ≤
              6 * (x.bs.length - rest'.length))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := chunkedHeaderSentLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with receivingCt1 := some d' } x.bs rest' (headerSentPolyCapBound x))
          (by dsimp only [chunkedHeaderSentLoopPre, chunkedHeaderSentPBCapAt];
              rw [optPolynomialDecoderPBAt_some_eq]; sep_entail)
        exact hcont d' rest' _ hpoly_res
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
          ⟨by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩

theorem chunkedHeaderSent_tag1_step_cl_placed [LibsignalPlacement]
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
    {x : ChunkedHeaderSentMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.HeaderSent} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hFit : FitsEnv M lim st (ChunkedHeaderSentMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (mergeMessage V1State.Unchunked.EkSent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.EkSent) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage V1State.Unchunked.EkSent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_302).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_302).rebase (blkPl_302).base H) (s0.readReg64 Reg.lr) s'
        (chunkedHeaderSentLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some uc' } x.bs rest' (headerSentPolyCapBound x))
        (WppPost (chunkedHeaderSentMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_302).base + 344#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
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
  let uc0 : V1State.Unchunked.EkSent := m.uc.getD default
  have hpush_exit := @chunkedHeaderSent_uc_push_exit_cl_placed _ M A lim H hPushCall x st R s0
    { uc := some uc0, sendingEk := m.sendingEk, receivingCt1 := m.receivingCt1 }
  have hfrom_push := @chunkedHeaderSent_uc_from_push_exit_cl_placed _ M A lim H hFromCall hPushCall x st R s0
    { uc := some uc0, sendingEk := m.sendingEk, receivingCt1 := m.receivingCt1 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedHeaderSent_uc_loop_ok_cl_placed _ M A lim H
      hFromCall hPushCall hVarintCall hSkipCall hAuthCall hBytesCall
      x st R s0 m.sendingEk m.receivingCt1 outerLimit innerLimit hFit hsp_align hbs_lt hlim_lt
  refine chunkedHeaderSent_uc_init_placed ?_ hpc hrun hsp hx20 hx23 hx24 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx0] at hx0_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1
  rw [hx22] at hx22_1; rw [hx25] at hx25_1
  obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply sepWPpLscro_of_vm (mid := lsmpl.base 291)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, spqrPoolAt,
        sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_decodeVarint2 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm])
      apply SepWP.exists_elim; intro evs
      apply SepWP.pure_elim; intro hevs
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      refine call_budget_lscro (x := (⟨x.bufRef, x.slot, restPtr, rest⟩, M.stepEvents evs st))
        (ret_pc := entry + 384#64) hVarintCall
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
      obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
      simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
        hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1]
        at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
      cases hdv0 : decodeVarint rest with
      | none =>
        have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
            (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSent_mergeField]
          simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
        apply sepWPpLscro_of_vm (mid := entry + 792#64)
        by_vm_steps
          (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
            stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
            sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
          apply SepWP.exists_elim; intro evs_dv
          apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
          have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          apply SepWP.fold
            (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr rest.length
              uc0 m.sendingEk m.receivingCt1)
            (by sep_focus)
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
              chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
                (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                { uc := some uc0, sendingEk := m.sendingEk, receivingCt1 := m.receivingCt1 } x.bs)
            (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
          exact hpush_exit hFit hnone (by omega) (by decide : 0 ≤ 2) hsm1 hsp_align
            (by simp only [arm64_norm, wp_norm])
            (by simp only [arm64_norm, wp_norm, hrunm])
            (by simp only [arm64_norm, wp_norm, hspm])
            (by simp only [arm64_norm, wp_norm, htrm, htr1])
            (by simp only [arm64_norm, wp_norm])
            ⟨by simp only [arm64_norm, wp_norm, hx27_m],
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
          have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
              (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
            apply hnone_of_uc
            rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSent_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint rest with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint rest = none := by
                rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint rest = some (len', rest0') := by
                rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
          apply sepWPpLscro_of_vm (mid := entry + 780#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, memRegion_48_cells1_160 s0.sp,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.exists_elim; intro v_stk0
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
            apply SepWP.fold
              (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr rest.length
                uc0 m.sendingEk m.receivingCt1)
              (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (Nat.le_refl (6 * (x.bs.length - rest.length)))
                hevs (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
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
                chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length))
                  (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
                  { uc := some uc0, sendingEk := m.sendingEk, receivingCt1 := m.receivingCt1 } x.bs)
              (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
            exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
              (by simp only [arm64_norm, wp_norm])
              (by simp only [arm64_norm, wp_norm, hrunm])
              (by simp only [arm64_norm, wp_norm, hspm])
              (by simp only [arm64_norm, wp_norm, htrm, htr1])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
        · have hule := ule_len_of_ge hlt_len hrest0_lt
          have hsub := bv_len_sub_limit hlt_len
          have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
          have hres0 : (mergeMessage V1State.Unchunked.EkSent.mergeField
              (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
              (mergeLoopBin V1State.Unchunked.EkSent.mergeField
                (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
                (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
            rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSent_mergeField]
            rcases hdv0_p : CryptoVerification.LibsignalSpqrV1.Proto.decodeVarint rest with e | ⟨len', rest0'⟩
            · have hdv0' : decodeVarint rest = none := by
                rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; nomatch hdv0'
            · have hdv0' : decodeVarint rest = some (len', rest0') := by
                rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
              rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
              have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
                conv_rhs => rw [hrest0_suf, List.drop_drop]
                congr 1; omega
              simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
                hdv0_p, Except.toOption, hlt_len, hdrop_eq]
              rcases mergeLoopBin V1State.Unchunked.EkSent.mergeField
                (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
          apply sepWPpLscro_of_vm (mid := entry + 464#64)
          by_vm_steps
            (conv => arg 4; simp only [decodeVarint2Spec, decodeVarint2SpecGen,
              stackAt_decodeVarint2_raw_eq, hdv0, sepExists_sepConj_left,
              sepExists_sepConj_right, sepConj_assoc, arm64_norm, wp_norm, hsp1])
            apply SepWP.exists_elim; intro evs_dv
            apply SepWP.pure_elim; rintro ⟨⟨htrm, hevs_dv⟩, hsm0, hsm1⟩
            apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
            apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
            apply SepWP.fold (unchunked3CapAt_mono A.repAlloc x.msgPtr uc0.epoch uc0.auth uc0.dk hrest0_le_rest) (by sep_focus)
            apply SepWP.fold
              (pool_entails_spqrPoolAt_nil A lim st (VmPreserved.refl sm)
                (by omega : 6 * (x.bs.length - rest.length) ≤ 6 * (x.bs.length - rest0.length))
                hevs (decodeVarint2Env_eq_nil_of_some hdv0 hevs_dv))
              (by sep_focus)
            (conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; simp only [sepConj_assoc])
            wp_steps
            apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
            apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
            rw [← spqrPoolAt_of_vmPreserved hvm2]
            apply SepWPpLscro.weaken_pre
              (P' := chunkedHeaderSentUcLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
                uc0 m.sendingEk m.receivingCt1 x.bs rest0 (headerSentPolyCapBound x))
              (by dsimp only [chunkedHeaderSentUcLoopPre, sliceCursorAfter]; sep_entail)
            exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _
              (Nat.le_refl _) hrest0_le hrest0_suf
              (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f => by
                have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by
                  rw [hr_suf, hr_eq]
                refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f
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
              (by simp only [arm64_norm, wp_norm, hx25_m])
              (by simp only [arm64_norm, wp_norm, hsm1, hsub])
              ⟨by simp only [arm64_norm, wp_norm, hx27_m],
               by simp only [arm64_norm, wp_norm, hx28_m],
               by simp only [arm64_norm, wp_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (mergeMessage V1State.Chunked.HeaderSent.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ekSent_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply sepWPpLscro_of_vm (mid := entry + 780#64)
    by_vm_steps
      (conv => arg 4; rw [chunkedHeaderSentUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
        sliceCursorAt, memRegion_48_wtErr160 s0.sp])
      (conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
      apply SepWP.exists_elim; intro b_wt1
      apply SepWP.exists_elim; intro b_wt0
      apply SepWP.exists_elim; intro v_wt0
      wp_steps
      apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold
        (unchunked3CapAt_entails_chunkedHeaderSentPBAt A.repAlloc x.msgPtr rest.length
          uc0 m.sendingEk m.receivingCt1)
        (by sep_focus)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
      rw [← spqrPoolAt_of_vmPreserved hvm1]
      apply SepWPpLscro.weaken_pre
        (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗
          memRegion (s0.sp - 120#64) 40 ∗
          stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗
          chunkedHeaderSentErrFrame A lim st (6 * (x.bs.length - rest.length))
            (headerSentPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { uc := some uc0, sendingEk := m.sendingEk, receivingCt1 := m.receivingCt1 } x.bs)
        (by dsimp only [chunkedHeaderSentErrFrame]; sep_entail)
      exact hfrom_push hFit hnone (by omega) (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
        (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hrun1])
        (by simp only [arm64_norm, wp_norm, hsp1])
        (by simp only [arm64_norm, wp_norm, htr1])
        ⟨by simp only [arm64_norm, wp_norm, hx27_1],
         by simp only [arm64_norm, wp_norm, hx28_1],
         by simp only [arm64_norm, wp_norm, hvregs_1]⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSentBudgetSteps
