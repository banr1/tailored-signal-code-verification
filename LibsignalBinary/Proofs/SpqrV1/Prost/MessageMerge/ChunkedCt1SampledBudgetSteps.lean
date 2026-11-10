/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp

/-!
# SPQR V1: Budget-Threaded Tag/Skip Step Proofs for `Chunked.Ct1Sampled::merge` (Block `300`)

Proves the budget-threaded `skip` (`tag ∉ {1, 2, 3}`), `tag = 1` (`uc : Option Unchunked.Ct1Sent`),
`tag = 2` (`sendingCt1 : Option PolynomialEncoder`), and `tag = 3`
(`receivingEk : Option PolynomialDecoder`) loop-body step lemmas for
`V1State.Chunked.Ct1Sampled::merge` (Block `300`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalProtoCodec (WireType skipField skip_length)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (IsDropSuffix SkipFieldGhost iwt_w0_setWidth8 pointsToBytes_prefix_join
   sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.LibsignalSpqrV1 (PolynomialDecoder PolynomialEncoder V1State)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Auth (WppPost)
open CryptoVerification.SpqrV1.ProtoRepr
  (chunkedCt1SampledPBAt optCt1SentPBAt optPolynomialDecoderPBAt optPolynomialEncoderPBAt
   polynomialDecoderPBAt polynomialEncoderPBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (ChunkedCt1SampledMergeGhost ChunkedLoopRegs PolyDecoderMergeGhost
   PolyEncoderMergeGhost SepWPpLscro
   bv64_add_zero bv64_sub_zero chunkedBelow chunkedBelow_eq_poly chunkedBelow_eq_unchunked
   chunkedBelow_skipField3_98 chunkedBelow_skipField3_98_entails
   chunkedCt1SampledMerge_fnOff chunkedCt1SampledPBCapAt
   chunkedCt1SampledPBCapAt_entails_pb chunkedCt1SampledPBCapAt_mono chunkedSavedRegs
   codecWireTypeToProto memRegion_48_split_128 optPolyDecoderPtsLen
   optPolyDecoder_getD_default_pts_len optPolyEncoderPolysLen optPolyEncoderPtsLen
   optPolyEncoder_getD_default_polys_len optPolyEncoder_getD_default_pts_len
   optUnchunkedCt1SentPBCapAt optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt
   optUnchunkedCt1SentPBCapAt_mono protoPolynomialDecoderAt_eq_pb
   protoPolynomialEncoderAt_eq_pb proto_mergeMessage_len_le setWidth8_ofNat64_wt
   unchunkedCt1SentPBCapAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (UnchunkedCt1SentMergeGhost)
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2 (blkPC_300 blkPl_300)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetAux
  (ct1SampledErrFrame ct1SampledLoopPre ct1Sampled_err0_ret_exit_placed
   ct1Sampled_push_err_exit_cl_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetInit
  (ct1Sampled_tag1_init_step_placed ct1Sampled_tag2_init_step_placed
   ct1Sampled_tag3_init_step_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (ChunkedCt1SampledMergeEnv FitsEnv.spqrMergeLoop_split SpqrMergeLoopEnv
   UnchunkedCt1SentMergeEnv UnchunkedCt1SentMergePostEnv
   chunkedCt1SampledMergeSpec ct1SampledPolyCapBound
   decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec unchunkedCt1SentMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedMergeBudgetKit
  (WppPanicFalse call_budget_lscro fitsEnv_skipField_of_spqr
   pool_entails_spqrPoolAt_append pool_entails_spqrPoolAt_nil pool_entails_spqrPoolAt_snoc
   sepWPpLscro_of_vm skipFieldEnv_eq_nil_of_some skipFieldEnv_to_spqr
   spqrPoolAt spqrPoolAt_of_vmPreserved vmPreserved_setMem_same)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (PolyDecoderMergeEnv PolyDecoderMergePostEnv PolyEncoderMergeEnv PolyEncoderMergePostEnv
   polyDecoderCapBound polyDecoderMergeSpec polyDecoderMergeSpecOfEnv
   polyEncoderCapBound polyEncoderMergeSpec polyEncoderMergeSpecOfEnv polyMergeLoopEnv_to_spqr)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff VmPreserved
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero
  chunkedCt1SampledMerge_fnOff setWidth8_ofNat64_wt

@[local simp, local arm64_norm]
private theorem iwt_w0_setWidth8_1 (iwt : WireType) :
    (BitVec.zeroExtend 64 ((BitVec.ofNat 64 iwt.toNat).setWidth 32)).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat :=
  (iwt_w0_setWidth8 iwt).1

@[local simp, local arm64_norm]
private theorem iwt_w0_trunc32_zext64_setWidth8 (iwt : WireType) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 iwt.toNat))).setWidth 8 =
      BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> decide

private theorem fitsEnv_unchunkedCt1Sent_of_spqr {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {f F maxLen polyBound : Nat} {x_uc : UnchunkedCt1SentMergeGhost} {evs : List AllocEvent}
    (hf : f + (4 * x_uc.bs.length + 8) ≤ F)
    (hlen : x_uc.bs.length ≤ maxLen)
    (hevs : SpqrMergeLoopEnv f maxLen polyBound evs)
    (hFit : FitsEnv M lim st (SpqrMergeLoopEnv F maxLen polyBound)) :
    FitsEnv M lim (M.stepEvents evs st) (UnchunkedCt1SentMergeEnv x_uc) := by
  have hrem := FitsEnv.spqrMergeLoop_split (f₂ := 4 * x_uc.bs.length + 8) hevs
    (hFit.mono fun _ h => h.mono_fuel hf)
  exact fun evs' hu => hrem evs' (hu.mono (Nat.le_refl _) hlen (Nat.zero_le _))

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
local notation "entry" => (blkPl_300).base

theorem ct1Sampled_skip_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
          (ct1SampledPolyCapBound x))
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 172#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_sf : SkipFieldGhost := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩
  have herr0_exit := @ct1Sampled_err0_ret_exit_placed _ M A lim H x st R s0 m
  apply sepWPpLscro_of_vm (mid := lsmpl.base 263)
  by_vm_steps
    (conv => arg 4; rw [ct1SampledLoopPre, spqrPoolAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedBelow_skipField3_98 s0.sp])
    (conv => arg 4; rw [sepExists_sepConj_left])
    apply SepWP.exists_elim; intro evs
    (conv => arg 4; rw [sepConj_assoc])
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; simp only [sepConj_assoc])
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
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0],
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
    cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
    | none =>
      have hnone := hnone_of_sf hsf
      apply sepWPpLscro_of_vm (mid := entry + 124#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_entails_pb A.repAlloc x.msgPtr rest.length m) (by sep_focus)
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
            memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗
            ct1SampledErrFrame A lim st (6 * (x.bs.length - rest.length) + 1)
              (ct1SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [ct1SampledErrFrame]; sep_entail)
        exact herr0_exit hnone (by omega) (by decide : 0 ≤ 3) hsm0 hsp_align
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
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [skipField3Spec, x_sf, hsf, sepExists_sepConj_left,
          sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_sf
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_sf
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp])
        apply SepWP.fold (chunkedBelow_skipField3_98_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (chunkedCt1SampledPBCapAt_mono A.repAlloc x.msgPtr m hrest'_le) (by sep_focus)
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
          (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr m x.bs rest'
            (ct1SampledPolyCapBound x))
          (by dsimp only [ct1SampledLoopPre]; sep_entail)
        exact hcont rest' _ hsf
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

theorem ct1Sampled_tag1_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hUcCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (u' : V1State.Unchunked.Ct1Sent) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (u', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with uc := some u' } x.bs rest' (ct1SampledPolyCapBound x))
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 368#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hpush_exit := fun {u' : V1State.Unchunked.Ct1Sent} =>
    @ct1Sampled_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0 { m with uc := some u' }
  refine ct1Sampled_tag1_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_uc : UnchunkedCt1SentMergeGhost :=
    ⟨iwt, x.msgPtr, m.uc.getD default, x.bufRef, x.slot, restPtr, rest⟩
  apply SepWPpLscro.weaken_pre
    (P' := spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
        (ct1SampledPolyCapBound x) s1 ∗
      unchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length (m.uc.getD default) ∗
      optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
      optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
    (Entails.of_eq (by sep_ac_rfl))
  apply sepWPpLscro_of_vm (mid := lsmpl.base 312)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedBelow_eq_unchunked s0.sp])
    (conv => arg 4; rw [sepExists_sepConj_left])
    apply SepWP.exists_elim; intro evs
    (conv => arg 4; rw [sepConj_assoc])
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_uc, M.stepEvents evs st))
      (ret_pc := entry + 416#64) hUcCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeSpecOfEnv, x_uc]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        hrest_lt,
        fitsEnv_unchunkedCt1Sent_of_spqr (x_uc := x_uc) (by dsimp only [x_uc]; omega)
          hrest_le hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases huc_res : (mergeMessage V1State.Unchunked.Ct1Sent.mergeField
        (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_uc huc_res
      apply sepWPpLscro_of_vm (mid := entry + 540#64)
      by_vm_steps
        (conv => arg 4; simp only [unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeSpecOfEnv,
          UnchunkedCt1SentMergePostEnv, x_uc, huc_res, hsp1, memRegion_48_split_128 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_u
        apply SepWP.exists_elim; intro u'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_u
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (4 * rest.length + 8)))
            hevs (hevs_u.mono (Nat.le_refl _) hrest_le (Nat.zero_le _)))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 604#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
            ct1SampledErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (4 * rest.length + 8))
              (ct1SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with uc := some u' } x.bs)
          (Entails.of_eq (by
            rw [chunkedBelow_eq_unchunked]
            dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt, optCt1SentPBAt, Reg.x0]
            sep_ac_rfl))
        exact hpush_exit hFit hnone (by omega) hsm0 hn_err hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨u', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le huc_res
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [unchunkedCt1SentMergeSpec, unchunkedCt1SentMergeSpecOfEnv,
          UnchunkedCt1SentMergePostEnv, x_uc, huc_res, hsp1,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_u
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_u
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (by omega : 6 * (x.bs.length - rest.length) + 4 * (rest.length - rest'.length) ≤
              6 * (x.bs.length - rest'.length))
            hevs (hevs_u.mono (Nat.le_refl _) hrest_le (Nat.zero_le _)))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply SepWPpLscro.weaken_pre
          (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with uc := some u' } x.bs rest' (ct1SampledPolyCapBound x))
          (Entails.of_eq (by
            dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt,
              optUnchunkedCt1SentPBCapAt]
            rw [chunkedBelow_eq_unchunked]
            sep_ac_rfl))
        exact hcont u' rest' _ huc_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

theorem ct1Sampled_tag2_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPolyEncCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyEncoderPtsLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hpolys_lt : optPolyEncoderPolysLen m.sendingCt1 + rest.length < 2 ^ 56)
    (hcap_bound : Nat.max (optPolyEncoderPtsLen m.sendingCt1) (optPolyEncoderPolysLen m.sendingCt1) +
      rest.length ≤ ct1SampledPolyCapBound x)
    (hnone_of_pe :
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pe' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = some (pe', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with sendingCt1 := some pe' } x.bs rest' (ct1SampledPolyCapBound x))
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hpush_exit := fun {pe' : PolynomialEncoder} =>
    @ct1Sampled_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
      { m with sendingCt1 := some pe' }
  refine ct1Sampled_tag2_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyEncoderMergeGhost :=
    ⟨iwt, x.msgPtr + 128#64, m.sendingCt1.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpoly_cap : polyEncoderCapBound x_poly ≤ ct1SampledPolyCapBound x := by
    dsimp only [polyEncoderCapBound, x_poly]
    rw [optPolyEncoder_getD_default_pts_len, optPolyEncoder_getD_default_polys_len]
    exact hcap_bound
  apply SepWPpLscro.weaken_pre
    (P' := spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
        (ct1SampledPolyCapBound x) s1 ∗
      polynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) (m.sendingCt1.getD default) ∗
      optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
      optPolynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) m.receivingEk ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
    (Entails.of_eq (by sep_ac_rfl))
  apply sepWPpLscro_of_vm (mid := lsmpl.base 297)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      ← protoPolynomialEncoderAt_eq_pb, chunkedBelow_eq_poly s0.sp])
    (conv => arg 4; rw [sepExists_sepConj_left])
    apply SepWP.exists_elim; intro evs
    (conv => arg 4; rw [sepConj_assoc])
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
      (ret_pc := entry + 356#64) hPolyEncCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv, x_poly]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        by change (m.sendingCt1.getD default).pts.length + rest.length < 2 ^ 56;
           rw [optPolyEncoder_getD_default_pts_len]; exact hpts_lt,
        by change (m.sendingCt1.getD default).polys.length + rest.length < 2 ^ 56;
           rw [optPolyEncoder_getD_default_polys_len]; exact hpolys_lt,
        fitsEnv_polyEncoderMerge_of_spqr (x_poly := x_poly)
          (by change 6 * (x.bs.length - rest.length) + (2 * rest.length + 2) ≤ 6 * x.bs.length + 12; omega)
          hrest_le hpoly_cap hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hpe_res : (mergeMessage PolynomialEncoder.mergeField
        (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_pe hpe_res
      apply sepWPpLscro_of_vm (mid := entry + 576#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_poly, hpe_res, hsp1, protoPolynomialEncoderAt_eq_pb,
          memRegion_48_split_128 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.exists_elim; intro pe'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A.repAlloc x.msgPtr rest.length m.uc)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (2 * rest.length + 2)))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 604#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
            ct1SampledErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (2 * rest.length + 2))
              (ct1SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with sendingCt1 := some pe' } x.bs)
          (Entails.of_eq (by
            rw [chunkedBelow_eq_poly]
            dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt,
              optPolynomialEncoderPBAt, Reg.x0]
            sep_ac_rfl))
        exact hpush_exit hFit hnone (by omega) hsm0 (by omega : n_err ≤ 2) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨pe', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpe_res
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [polyEncoderMergeSpec, polyEncoderMergeSpecOfEnv,
          PolyEncoderMergePostEnv, x_poly, hpe_res, hsp1, protoPolynomialEncoderAt_eq_pb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
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
          (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with sendingCt1 := some pe' } x.bs rest' (ct1SampledPolyCapBound x))
          (Entails.of_eq (by
            dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt,
              optPolynomialEncoderPBAt]
            rw [chunkedBelow_eq_poly]
            sep_ac_rfl))
        exact hcont pe' rest' _ hpe_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

theorem ct1Sampled_tag3_step_cl_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hPolyDecCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)))
    (hPushCall : subroutine_ok ((blkPC_300).rebase (blkPl_300).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)))
    {x : ChunkedCt1SampledMergeGhost} {st : M.σ} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.Ct1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hFit : FitsEnv M lim st (ChunkedCt1SampledMergeEnv x))
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_suf : IsDropSuffix x.bs rest)
    (hpts_lt : optPolyDecoderPtsLen m.receivingEk + rest.length < 2 ^ 56)
    (hcap_bound : optPolyDecoderPtsLen m.receivingEk + rest.length ≤ ct1SampledPolyCapBound x)
    (hnone_of_pd :
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = none →
      (mergeMessage V1State.Chunked.Ct1Sampled.mergeField
        (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (pd' : PolynomialDecoder) (rest' : List (BitVec 8)) (s' : State),
      (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption = some (pd', rest') →
      s'.pc = (blkPl_300).base + 192#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      ChunkedLoopRegs s0 s' →
      SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s'
        (ct1SampledLoopPre A lim st s0 s' x.msgPtr x.bufRef x.slot x.ptr
          { m with receivingEk := some pd' } x.bs rest' (ct1SampledPolyCapBound x))
        (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R))
    (hpc : s.pc = (blkPl_300).base + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : ChunkedLoopRegs s0 s) :
    SepWPpLscro lsmpl ((blkPC_300).rebase (blkPl_300).base H) (s0.readReg64 Reg.lr) s
      (ct1SampledLoopPre A lim st s0 s x.msgPtr x.bufRef x.slot x.ptr m x.bs rest
        (ct1SampledPolyCapBound x))
      (WppPost (chunkedCt1SampledMergeSpec A lim) (x, st) R s0) (WppPanicFalse R) := by
  have hpush_exit := fun {pd' : PolynomialDecoder} =>
    @ct1Sampled_push_err_exit_cl_placed _ M A lim H hPushCall x st R s0
      { m with receivingEk := some pd' }
  refine ct1Sampled_tag3_init_step_placed hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs ?_
  clear hpc hrun hsp htr hx0 hx19 hx20 hx21 hx22 hcs s
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hcs1
  obtain ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  let x_poly : PolyDecoderMergeGhost :=
    ⟨iwt, x.msgPtr + 184#64, m.receivingEk.getD default, x.bufRef, x.slot, restPtr, rest⟩
  have hpoly_cap : polyDecoderCapBound x_poly ≤ ct1SampledPolyCapBound x := by
    dsimp only [polyDecoderCapBound, x_poly]
    rw [optPolyDecoder_getD_default_pts_len]
    exact hcap_bound
  apply SepWPpLscro.weaken_pre
    (P' := spqrPoolAt A lim st (6 * (x.bs.length - rest.length)) x.bs.length
        (ct1SampledPolyCapBound x) s1 ∗
      polynomialDecoderPBAt A.repAlloc (x.msgPtr + 184#64) (m.receivingEk.getD default) ∗
      optUnchunkedCt1SentPBCapAt A.repAlloc x.msgPtr rest.length m.uc ∗
      optPolynomialEncoderPBAt A.repAlloc (x.msgPtr + 128#64) m.sendingCt1 ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAfter x.slot x.ptr x.bs rest ∗
      memRegion (s0.sp - 128#64) 48 ∗ chunkedBelow s0.sp ∗ chunkedSavedRegs s0)
    (Entails.of_eq (by sep_ac_rfl))
  apply sepWPpLscro_of_vm (mid := lsmpl.base 296)
  by_vm_steps
    (conv => arg 4; rw [spqrPoolAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      ← protoPolynomialDecoderAt_eq_pb, chunkedBelow_eq_poly s0.sp])
    (conv => arg 4; rw [sepExists_sepConj_left])
    apply SepWP.exists_elim; intro evs
    (conv => arg 4; rw [sepConj_assoc])
    apply SepWP.pure_elim; intro hevs
    (conv => arg 4; simp only [sepConj_assoc])
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨by simp only [arm64_norm, wp_norm], fun hvm1 => ?_⟩
    refine call_budget_lscro (x := (x_poly, M.stepEvents evs st))
      (ret_pc := entry + 304#64) hPolyDecCall
      (by simp only [arm64_norm, wp_norm]) (by simp only [arm64_norm, wp_norm, hrun1])
      (by simp only [State.spAligned, arm64_norm, wp_norm, hsp1]; exact hsp_align)
      (by simp only [arm64_norm, wp_norm])
      (by conv =>
            lhs
            dsimp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv, x_poly]
            simp only [sepConj_assoc]
            arg 2
            simp only [A.pool_of_vmPreserved hvm1, arm64_norm, wp_norm, hsp1])
      (by exact ⟨by simp only [arm64_norm, wp_norm, hx0_1],
        by simp only [arm64_norm, wp_norm, hx20_1],
        by simp only [arm64_norm, wp_norm, hx19_1],
        by change (m.receivingEk.getD default).pts.length + rest.length < 2 ^ 56;
           rw [optPolyDecoder_getD_default_pts_len]; exact hpts_lt,
        fitsEnv_polyDecoderMerge_of_spqr (x_poly := x_poly)
          (by change 6 * (x.bs.length - rest.length) + (2 * rest.length + 2) ≤ 6 * x.bs.length + 12; omega)
          hrest_le hpoly_cap hevs hFit⟩)
      (by sep_focus) ?_
    intro sm hpcm hrunm hspm hcsm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, wp_norm, hsp1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hvregs_1]
      at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
    cases hpd_res : (mergeMessage PolynomialDecoder.mergeField
        (codecWireTypeToProto iwt) (m.receivingEk.getD default) rest 98).toOption with
    | none =>
      have hnone := hnone_of_pd hpd_res
      apply sepWPpLscro_of_vm (mid := entry + 504#64)
      by_vm_steps
        (conv => arg 4; simp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv,
          PolyDecoderMergePostEnv, x_poly, hpd_res, hsp1, protoPolynomialDecoderAt_eq_pb,
          memRegion_48_split_128 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.exists_elim; intro evs_p
        apply SepWP.exists_elim; intro pd'
        apply SepWP.exists_elim; intro n_err
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        wp_focus_pure; intro hn_err
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        apply SepWP.fold
          (optUnchunkedCt1SentPBCapAt_entails_optCt1SentPBAt A.repAlloc x.msgPtr rest.length m.uc)
          (by sep_focus)
        apply SepWP.fold
          (pool_entails_spqrPoolAt_append A lim st (VmPreserved.refl sm)
            (Nat.le_refl (6 * (x.bs.length - rest.length) + (2 * rest.length + 2)))
            hevs (polyMergeLoopEnv_to_spqr hrest_le hpoly_cap hevs_p))
          (by sep_focus)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [arm64_norm, wp_norm], fun hvm2 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm2]
        apply sepWPpLscro_of_vm (mid := entry + 604#64)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine ⟨by simp only [vmPreserved_setMem_same, arm64_norm, wp_norm], fun hvm3 => ?_⟩
        rw [← spqrPoolAt_of_vmPreserved hvm3]
        apply SepWPpLscro.weaken_pre
          (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
            decodeErrorAtStackLen A.repAlloc (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
            memRegion (s0.sp - 120#64) 40 ∗ chunkedBelow s0.sp ∗
            ct1SampledErrFrame A lim st
              (6 * (x.bs.length - rest.length) + (2 * rest.length + 2))
              (ct1SampledPolyCapBound x) s0 _ x.msgPtr x.bufRef x.slot x.ptr
              { m with receivingEk := some pd' } x.bs)
          (Entails.of_eq (by
            rw [chunkedBelow_eq_poly]
            dsimp only [ct1SampledErrFrame, chunkedCt1SampledPBAt,
              optPolynomialDecoderPBAt, Reg.x0]
            sep_ac_rfl))
        exact hpush_exit hFit hnone (by omega) hsm0 (by omega : n_err ≤ 2) hsp_align
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hspm])
          ⟨by simp only [arm64_norm, wp_norm, hx26_m],
           by simp only [arm64_norm, wp_norm, hx27_m],
           by simp only [arm64_norm, wp_norm, hx28_m],
           by simp only [arm64_norm, wp_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨pd', rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := proto_mergeMessage_len_le hpd_res
      apply sepWPpLscro_of_vm (mid := entry + 192#64)
      by_vm_steps
        (conv => arg 4; simp only [polyDecoderMergeSpec, polyDecoderMergeSpecOfEnv,
          PolyDecoderMergePostEnv, x_poly, hpd_res, hsp1, protoPolynomialDecoderAt_eq_pb,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro evs_p
        wp_focus_pure; intro htrm
        wp_focus_pure; intro hevs_p
        wp_focus_pure; intro hsm0
        (conv => arg 4; simp only [arm64_norm, wp_norm, hsp1])
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (optUnchunkedCt1SentPBCapAt_mono A.repAlloc x.msgPtr m.uc hrest'_le) (by sep_focus)
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
          (P' := ct1SampledLoopPre A lim st s0 _ x.msgPtr x.bufRef x.slot x.ptr
            { m with receivingEk := some pd' } x.bs rest' (ct1SampledPolyCapBound x))
          (Entails.of_eq (by
            dsimp only [ct1SampledLoopPre, chunkedCt1SampledPBCapAt,
              optPolynomialDecoderPBAt]
            rw [chunkedBelow_eq_poly]
            sep_ac_rfl))
        exact hcont pd' rest' _ hpd_res
          (by simp only [arm64_norm, wp_norm])
          (by simp only [arm64_norm, wp_norm, hrunm])
          (by simp only [arm64_norm, wp_norm, hspm])
          (by simp only [arm64_norm, wp_norm, htrm, htr1])
          (by simp only [arm64_norm, wp_norm, hx19_m])
          (by simp only [arm64_norm, wp_norm, hx20_m])
          (by simp only [arm64_norm, wp_norm, hx21_m])
          (by simp only [arm64_norm, wp_norm, hx22_m])
          ⟨by simp only [arm64_norm, wp_norm, hx23_m],
           by simp only [arm64_norm, wp_norm, hx24_m],
           by simp only [arm64_norm, wp_norm, hx25_m],
           ⟨by simp only [arm64_norm, wp_norm, hx26_m],
            by simp only [arm64_norm, wp_norm, hx27_m],
            by simp only [arm64_norm, wp_norm, hx28_m],
            by simp only [arm64_norm, wp_norm, hvregs_m]⟩⟩

end ClPlaced

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1SampledBudgetSteps
