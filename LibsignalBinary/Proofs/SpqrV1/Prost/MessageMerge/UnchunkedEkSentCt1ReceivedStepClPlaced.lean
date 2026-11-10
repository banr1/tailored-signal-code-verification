/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Step Lemmas for `unchunked::EkSentCt1Received::merge` (Block `311`)

Code-loaded (`withLsCodeRoLoaded lsmpl`) `[LibsignalPlacement]` exit and per-field step lemmas for
`prost::encoding::message::merge::<unchunked::EkSentCt1Received, &mut &[u8]>` (Block `311`).
-/

@[expose] public section
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlaced

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
  (LibsignalPlacement lsmpl blkPC_311 blkPl_311)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim SepWPp.pure_elim bv64_sub_zero bv64_add_zero
  WppPost WppPanic setWidth8_ofNat64_wt mergeBytes_suffix
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero_u bv64_add_zero_u unchunkedEkSentCt1ReceivedMerge_fnOff

theorem ekSent_from_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {w : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 108#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hcs : HighCalleeSaved24 s0 s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ w) ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv ?_
  conv => arg 4; rw [unchunkedMergeBelow_err s0.sp, ekSentErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := (s0.sp - 112#64, w))
    (ret_pc := (blkPl_311).base + 116#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost unchunkedEkSentCt1ReceivedMergeOwnSpec
  simp only [decodeErrorFromSpec, hnone, stackAt_unchunkedMerge s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro m'
  apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le2 A _) (by sep_focus)
  apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedAt_entails_exists A x.msgPtr m') (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_112 s0.sp) (by sep_focus)
  wp_done

theorem ekSent_push_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hn : n ≤ 1)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 656#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 112#64)
    (hcs : HighCalleeSaved24 s0 s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 112#64) ↦₆₄ err) ∗
        decodeErrorAtStackLen A err n ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv ?_
  conv => arg 4; rw [unchunkedMergeBelow_err s0.sp, ekSentErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := (s0.sp - 112#64, err, n))
    (ret_pc := (blkPl_311).base + 660#64) hPushCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by omega : n < 2 ^ 32)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost unchunkedEkSentCt1ReceivedMergeOwnSpec
  simp only [decodeErrorPushSpec, hnone, stackAt_unchunkedMerge s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro m'
  apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_succ_le1_entails_le2 A err hn) (by sep_focus)
  apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedAt_entails_exists A x.msgPtr m') (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_112 s0.sp err) (by sep_focus)
  wp_done

theorem ekSent_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @ekSent_err0_ret_exit_placed _ A H x R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv ?_
  conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    unchunkedMergeBelow_eq_authMergeStack s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_311).base + 328#64) hSkipCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [skipField3Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := (blkPl_311).base + 120#64)
    conv => arg 4; simp only [skipField3Spec, hsf, ← unchunkedMergeBelow_eq_authMergeStack, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr rest.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
    conv => arg 4; simp only [skipField3Spec, hsf, ← unchunkedMergeBelow_eq_authMergeStack, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' := ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [ekSentLoopPre]; sep_entail)
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_tag1_push_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {err : BitVec 64}
    (hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_311).base + 552#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = err)
    (hcs : HighCalleeSaved24 s0 s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ A H hPushCall x R s0
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 656#64) hinv ?_
  conv => arg 4; rw [memRegion_48_split_112 s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v_stk0
  wp_steps
  wp_reach; intro hinv_c
  apply SepWPp.weaken_pre (P' :=
    ((s0.sp - 112#64) ↦₆₄ err) ∗
      decodeErrorAtStackLen A err 0 ∗
      memRegion (s0.sp - 104#64) 40 ∗
      unchunkedMergeBelow s0.sp ∗
      ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [ekSentErrFrame]; sep_entail)
  exact hpush_exit hnone herr (Nat.zero_le 1) hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
    (by simp only [arm64_norm, hsp])
    ⟨by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
     by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
     by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinv_c

theorem ekSent_tag1_wt_err_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType}
    (hiwt : iwt ≠ .varint)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone : (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hcs : HighCalleeSaved24 s0 s)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @ekSent_tag1_push_exit_cl_placed _ A H hPushCall x R s0
  have hcbnz := iwt_cbnz_true_of_ne_varint_u hiwt
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv ?_
  conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    sliceCursorAt, memRegion_48_wtErr112 s0.sp, unchunkedMergeBelow_err s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro b_wt1
  apply SepWP.exists_elim; intro b_wt0
  apply SepWP.exists_elim; intro v_wt0
  wp_steps
  apply SepWP.fold (wtErr112_entails_memRegion40 s0.sp _ _) (by sep_focus)
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := (s0.sp - 112#64, 0x8000000000000006#64))
    (ret_pc := (blkPl_311).base + 548#64) hFromCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    (by decide : KindNoHeap 0x8000000000000006#64)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 552#64) hinv_m ?_
  conv => arg 4; simp only [decodeErrorFromSpec, sepConj_assoc, arm64_norm, hsp]
  apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
  apply SepWP.fold (unchunkedMergeBelow_err_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_112 s0.sp) (by sep_focus)
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
  apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
  apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr rest.length m) (by sep_focus)
  wp_steps
  wp_reach; intro hinv_n
  apply SepWPp.weaken_pre (P' :=
    decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
      memRegion (s0.sp - 112#64) 48 ∗
      unchunkedMergeBelow s0.sp ∗
      ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
    (by dsimp only [ekSentErrFrame]; sep_entail)
  exact htag1_push hnone hve_ne hsp_align
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
    (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
    (by simp only [arm64_norm])
    ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
     by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
     by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_tag1_varint_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_dv : decodeVarint rest = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 340#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have htag1_push := @ekSent_tag1_push_exit_cl_placed _ A H hPushCall x R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv ?_
  conv => arg 4; rw [ekSentLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, unchunkedMergeBelow_leaf s0.sp]; simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_311).base + 352#64) hVarintCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hrest_lt
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hdv : decodeVarint rest with
  | none =>
    have hnone := hnone_of_dv hdv
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 552#64) hinv_m ?_
    conv => arg 4; simp only [decodeVarint2Spec, hdv, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
    apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (protoUnchunkedEkSentCt1ReceivedCapAt_entails_exists A x.msgPtr rest.length m) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗
        memRegion (s0.sp - 112#64) 48 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact htag1_push hnone hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
    conv => arg 4; simp only [decodeVarint2Spec, hdv, protoUnchunkedEkSentCt1ReceivedCapAt,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (unchunkedMergeBelow_leaf_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A x.msgPtr m.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A (x.msgPtr + 0x18#64) m.ct1 hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_mono A (x.msgPtr + 0x30#64) m.auth hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with epoch := v } x.bs rest')
      (by dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]; sep_entail)
    exact hcont v rest' _ hdv
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_tag2_call_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 252#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (vecU8CapAt A x.msgPtr rest.length m.dk ∗
        vecU8CapAt A (x.msgPtr + 0x18#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A (x.msgPtr + 0x30#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x60#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        A.pool ∗
        memRegion (s0.sp - 112#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        unchunkedMergeBelow s0.sp)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ A H hPushCall x R s0
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 295) hinv ?_
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf,
    unchunkedMergeBelow_eq_authMergeStack s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨iwt, x.msgPtr + 0x30#64, m.auth.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_311).base + 264#64) hAuthCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [authMergeSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    hrest_lt
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [authMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan)
    ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases ham : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption with
  | none =>
    have hnone := hnone_of_am ham
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 656#64) hinv_m ?_
    conv => arg 4; simp only [authMergeSpec, ham, memRegion_48_split_112 s0.sp,
      ← unchunkedMergeBelow_eq_authMergeStack,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.exists_elim; intro m_auth'
    apply SepWP.exists_elim; intro n_err
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hn_err⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8_u A x.msgPtr rest.length m.dk) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8_u A (x.msgPtr + 0x18#64) rest.length m.ct1) (by sep_focus)
    apply SepWP.fold (authenticatorPBAt_entails_optExists A (x.msgPtr + 0x30#64) m_auth') (by sep_focus)
    apply SepWP.fold (ekSent_parts_entails_exists A x.msgPtr m.dk m.ct1 m.epoch) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hpush_exit hnone hsm0 hn_err hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix ham).1
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
    conv => arg 4; simp only [authMergeSpec, ham, ← unchunkedMergeBelow_eq_authMergeStack,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A x.msgPtr m.dk hrest'_le) (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A (x.msgPtr + 0x18#64) m.ct1 hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
      (by dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, optProtoAuthenticatorCapAt]; sep_entail)
    exact hcont v rest' _ ham
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

theorem ekSent_tag2_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_am : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : ProtoAuthenticator) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto iwt) (m.auth.getD default) rest 97).toOption = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' →
      LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with auth := some v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  have hcall := fun {s_c} => @ekSent_tag2_call_step_cl_placed _ A H hPushCall hAuthCall x R s0 s_c m rest iwt limit
    hsp_align hrest_le hrest_lt hrest_suf hnone_of_am hcont
  cases hauth : m.auth with
  | none =>
    have h56 : (x.msgPtr + 0x30#64) + 8#64 = x.msgPtr + 56#64 := by bv_lin
    have h64 : (x.msgPtr + 0x30#64) + 16#64 = x.msgPtr + 64#64 := by bv_lin
    have h72 : (x.msgPtr + 0x30#64) + 24#64 = x.msgPtr + 72#64 := by bv_lin
    have h80 : (x.msgPtr + 0x30#64) + 32#64 = x.msgPtr + 80#64 := by bv_lin
    have h88 : (x.msgPtr + 0x30#64) + 40#64 = x.msgPtr + 88#64 := by bv_lin
    have h48 : x.msgPtr + 0x30#64 = x.msgPtr + 48#64 := rfl
    have hdef_cap := default_auth_cells_entails_cap A (x.msgPtr + 0x30#64) rest.length
    rw [h56, h64, h72, h80, h88] at hdef_cap
    conv at hdef_cap => arg 1; rw [h48]
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 252#64) hinv ?_
    conv => arg 4; rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, hauth,
      optProtoAuthenticatorCapAt, memRegion_40_split_5_cells (x.msgPtr + 0x30#64),
      h56, h64, h72, h80, h88, h48]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v4
    apply SepWP.exists_elim; intro v3
    apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v1
    wp_steps
    apply SepWP.fold hdef_cap (by sep_focus)
    wp_reach; intro hinv_c
    apply SepWPp.weaken_pre (P' :=
      vecU8CapAt A x.msgPtr rest.length m.dk ∗
        vecU8CapAt A (x.msgPtr + 0x18#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A (x.msgPtr + 0x30#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x60#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        A.pool ∗
        memRegion (s0.sp - 112#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        unchunkedMergeBelow s0.sp)
      (by simp only [hauth, Option.getD_none]; sep_entail)
    exact hcall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      ⟨by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinv_c
  | some auth0 =>
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 252#64) hinv ?_
    conv => arg 4; rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, hauth,
      optProtoAuthenticatorCapAt, authenticatorPBCapAt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro cap2
    apply SepWP.exists_elim; intro ptr2
    apply SepWP.exists_elim; intro cap1
    apply SepWP.exists_elim; intro ptr1
    conv => arg 4; rw [vecU8At, vecHeader]; simp only [sepConj_assoc, arm64_norm]
    apply SepWP.pure_elim; rintro ⟨hcap1_ok, ⟨hcap1_len, hcap1_lt, hptr1_ne⟩, hcap2_ok⟩
    obtain ⟨hcmn1, hcmn2⟩ := cap_add_one_ne_zero_of_lt63 hcap1_lt
    wp_steps
    have hrepack :
        (((x.msgPtr + 48#64) ↦₆₄ cap1) ∗
          ((x.msgPtr + 56#64) ↦₆₄ ptr1) ∗
          ((x.msgPtr + 64#64) ↦₆₄ BitVec.ofNat 64 auth0.rootKey.length) ∗
          (if cap1 = 0 then emp else A.live ptr1 cap1.toNat 1 ∗ (ptr1 ↦ₛ auth0.rootKey) ∗
            memRegion (ptr1 + BitVec.ofNat 64 auth0.rootKey.length) (cap1.toNat - auth0.rootKey.length))) ∗
          vecU8At A (x.msgPtr + 72#64) cap2 ptr2 auth0.macKey ⊢
        authenticatorPBCapAt A (x.msgPtr + 0x30#64) rest.length auth0 := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans ?_ (Entails.sepExists_intro cap1)
        refine Entails.trans ?_ (Entails.sepExists_intro ptr1)
        unfold vecU8At vecHeader
        have h56 : (x.msgPtr + 0x30#64) + 8#64 = x.msgPtr + 56#64 := by bv_lin
        have h64 : (x.msgPtr + 0x30#64) + 16#64 = x.msgPtr + 64#64 := by bv_lin
        have h48 : x.msgPtr + 0x30#64 = x.msgPtr + 48#64 := rfl
        have hpure1 : auth0.rootKey.length ≤ cap1.toNat ∧ cap1.toNat < 2 ^ 63 ∧ ptr1 ≠ 0 :=
          ⟨hcap1_len, hcap1_lt, hptr1_ne⟩
        rw [h56, h64, h48]
        simp only [hcap1_ok, eq_true hpure1, pure_true, emp_sepConj, sepConj_assoc]
        exact Entails.refl _
      · refine Entails.trans ?_ (Entails.sepExists_intro cap2)
        refine Entails.trans ?_ (Entails.sepExists_intro ptr2)
        have h72 : (x.msgPtr + 0x30#64) + 0x18#64 = x.msgPtr + 72#64 := by bv_lin
        rw [h72]
        simp only [hcap2_ok, pure_true, emp_sepConj]
        exact Entails.refl _
    apply SepWP.fold hrepack (by sep_focus)
    wp_reach; intro hinv_c
    apply SepWPp.weaken_pre (P' :=
      vecU8CapAt A x.msgPtr rest.length m.dk ∗
        vecU8CapAt A (x.msgPtr + 0x18#64) rest.length m.ct1 ∗
        authenticatorPBCapAt A (x.msgPtr + 0x30#64) rest.length (m.auth.getD default) ∗
        ((x.msgPtr + 0x60#64) ↦₆₄ m.epoch) ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr x.bs rest ∗
        A.pool ∗
        memRegion (s0.sp - 112#64) 48 ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        memRegion (s0.sp - 40#64) 8 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        unchunkedMergeBelow s0.sp)
      (by simp only [hauth, Option.getD_some]; sep_entail)
    exact hcall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx0]) (by simp only [arm64_norm, hx19])
      (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23])
      ⟨by simp only [arm64_norm, hx24], by simp only [arm64_norm, hx25],
       by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27],
       by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩ hinv_c

theorem ekSent_tag3_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_311).rebase (blkPl_311).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : UnchunkedEkSentCt1ReceivedMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Unchunked.EkSentCt1Received} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage V1State.Unchunked.EkSentCt1Received.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_311).base + 152#64 →
      s'.status = .Running →
      s'.sp = s0.sp - 112#64 →
      s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef →
      s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot →
      s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 →
      HighCalleeSaved24 s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s'
        (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with dk := v } x.bs rest')
        (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
        (WppPanic R s0))
    (hpc : s.pc = (blkPl_311).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64)
    (hcs : HighCalleeSaved24 s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_311).rebase (blkPl_311).base H) (s0.readReg64 Reg.lr) s
      (ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (unchunkedEkSentCt1ReceivedMergeOwnSpec A) x R s0)
      (WppPanic R s0) := by
  obtain ⟨hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @ekSent_push_err_exit_cl_placed _ A H hPushCall x R s0
  conv =>
    arg 4
    rw [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt, vecU8CapAt,
      sliceCursorAfter_eq_split hrest_le hrest_suf,
      unchunkedMergeBelow_bytesMerge3 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap1
  apply SepWPp.exists_elim; intro ptr1
  apply SepWPp.pure_elim; intro hcap1
  refine SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv ?_
  wp_steps
  wp_reach; intro hinv_c
  refine SepWPp.call_frame_lscro (hinv := hinv_c) (x := ⟨iwt, x.msgPtr, cap1, ptr1, m.dk, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_311).base + 384#64) hBytesCall
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinv_m
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 656#64) hinv_m ?_
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_112 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hdk : vecU8At A x.msgPtr cap1 ptr1 m.dk ⊢ vecU8 A x.msgPtr m.dk :=
      Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
    apply SepWP.fold hdk (by sep_focus)
    apply SepWP.fold (vecU8CapAt_entails_vecU8_u A (x.msgPtr + 0x18#64) rest.length m.ct1) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_entails_optProtoAuthenticatorAt A (x.msgPtr + 0x30#64) rest.length m.auth) (by sep_focus)
    apply SepWP.fold (ekSent_fields_entails_exists A x.msgPtr m) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 112#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 104#64) 40 ∗
        unchunkedMergeBelow s0.sp ∗
        ekSentErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.bs)
      (by dsimp only [ekSentErrFrame]; sep_entail)
    exact hpush_exit hnone hsm0 (Nat.zero_le 1) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
    refine SepWPp.of_sepWP_lscro (mid := (blkPl_311).base + 152#64) hinv_m ?_
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap1'
    apply SepWP.exists_elim; intro ptr1'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (unchunkedMergeBelow_bytesMerge3_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hdk_cap : vecU8At A x.msgPtr cap1' ptr1' v ⊢ vecU8CapAt A x.msgPtr rest'.length v := by
      unfold vecU8CapAt
      refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
      exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
    apply SepWP.fold hdk_cap (by sep_focus)
    apply SepWP.fold (vecU8CapAt_mono_u A (x.msgPtr + 0x18#64) m.ct1 hrest'_le) (by sep_focus)
    apply SepWP.fold (optProtoAuthenticatorCapAt_mono A (x.msgPtr + 0x30#64) m.auth hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinv_n
    apply SepWPp.weaken_pre (P' :=
      ekSentLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with dk := v } x.bs rest')
      (by dsimp only [ekSentLoopPre, protoUnchunkedEkSentCt1ReceivedCapAt]; sep_entail)
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m])
      ⟨by simp only [arm64_norm, hx24_m], by simp only [arm64_norm, hx25_m],
       by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m],
       by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinv_n

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1ReceivedStepClPlaced
