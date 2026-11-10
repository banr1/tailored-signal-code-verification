/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.MergePlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded `[LibsignalPlacement]` Proof of `Authenticator::merge` (Block `295`)

Code-loaded `[LibsignalPlacement]` step lemmas, loop invariant (`auth_loop_ok_cl_placed`), and
subroutine contracts for `prost::encoding::message::merge::<Authenticator, &mut &[u8]> [local#2]`
(Block `295`) against `withLsCodeRoLoaded lsmpl (authMergeSpec A)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlaced

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.SpqrV1.Auth

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero

/-! ## Exit and Field Step Lemmas -/

theorem auth_from_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {w v_stk0 : BitVec 64}
    (hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = w)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := (s0.sp - 96#64, w))
    (ret_pc := (blkPl_295).base + 112#64) hFromCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorFromSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpec
  simp only [decodeErrorFromSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48 s0.sp) (by sep_focus)
  wp_done

theorem auth_push_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {err : BitVec 64}
    (hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_295).base + 436#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 96#64)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 96#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [skipBelow3_err s0.sp 97 (by decide), authErrFrame]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := (s0.sp - 96#64, err, 0))
    (ret_pc := (blkPl_295).base + 440#64) hPushCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl)
    (by decide : 0 < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hspm hx19 hx20 hx21 hx22 hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp hvregs_m
  apply SepWPp.of_sepWP_ret
  unfold WppPost authMergeSpec
  simp only [decodeErrorPushSpec, hnone, authMergeStack, stackAt_skipField3 _ 97 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.fold (skipBelow3_err_entails s0.sp 97 (by decide)) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (authenticatorPBAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48 s0.sp err) (by sep_focus)
  wp_done

theorem auth_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 96 tag iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 96 tag iwt rest = some rest' →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (authMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_295).base + 140#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @auth_err0_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    skipBelow3_97_eq_stackAt_96 s0.sp]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, tag, 96, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_295).base + 152#64) hSkipCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 96 < 2 ^ 32 ∧ rest.length < 2 ^ 63)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [skipField3Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 96 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := (blkPl_295).base + 116#64)
    conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr rest.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    conv => arg 4; simp only [skipField3Spec, hsf, ← skipBelow3_97_eq_stackAt_96, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem auth_tag1_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
        (WppPost (authMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_295).base + 252#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @auth_push_err_exit_cl_placed _ A H hPushCall x R s0
  conv =>
    arg 4
    rw [authLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, x.msgPtr, cap1, ptr1, m.rootKey, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_295).base + 264#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap1⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap1 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps
    wp_reach; intro hinvm'
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm'
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap2' : BytesMergeCapOk cap2 rest'.length := bytesMergeCapOk_mono hcap2 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap1'; apply SepWP.exists_elim; intro ptr1'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap1'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A x.msgPtr cap1' ptr1' v ∗ vecU8At A (x.msgPtr + 0x18#64) cap2 ptr2 m.macKey ⊢
          authenticatorPBCapAt A x.msgPtr rest'.length { m with rootKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1' (Entails.sepExists_right ptr1' (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' :=
      authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with rootKey := v } x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem auth_tag2_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63)
    (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none)
    (hcont : ∀ (v rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_295).base + 160#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
        (WppPost (authMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_295).base + 228#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @auth_push_err_exit_cl_placed _ A H hPushCall x R s0
  conv =>
    arg 4
    rw [authLoopPre, authenticatorPBCapAt, sliceCursorAfter_eq_split hrest_le hrest_suf,
      skipBelow3_bytesMerge3 s0.sp 97 (by decide) (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap2; apply SepWPp.exists_elim; intro ptr2
  apply SepWPp.exists_elim; intro cap1; apply SepWPp.exists_elim; intro ptr1
  apply CryptoVerification.SpqrV1.Auth.SepWPp.pure_elim; intro hcap1; apply SepWPp.pure_elim2; intro hcap2
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, x.msgPtr + 0x18#64, cap2, ptr2, m.macKey, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_295).base + 240#64) hBytesCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19, hx20, setWidth8_ofNat64_wt]; rfl)
    (⟨hrest_lt, hcap2⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk cap2 rest.length)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [bytesMerge3RawSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hmb : mergeBytes iwt rest with
  | none =>
    have hnone := hnone_of_mb hmb
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 436#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, memRegion_48_split_96 s0.sp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    have hpb : vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 24#64) cap2 ptr2 m.macKey ⊢
        authenticatorPBAt A x.msgPtr m :=
      sepConj_mono
        (Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _)))
        (Entails.sepExists_right cap2 (Entails.sepExists_right ptr2 (Entails.refl _)))
    apply SepWP.fold hpb (by sep_focus)
    wp_steps
    wp_reach; intro hinvm'
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗
        memRegion (s0.sp - 88#64) 40 ∗ skipBelow3 s0.sp 97 ∗
        authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (Entails.of_eq (by dsimp only [authErrFrame]; ac_rfl))
    exact hpush_exit hnone hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm'
  | some p =>
    rcases p with ⟨v, rest'⟩
    have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (mergeBytes_length hmb)
    have hcap1' : BytesMergeCapOk cap1 rest'.length := bytesMergeCapOk_mono hcap1 hrest'_le
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
    conv => arg 4; simp only [bytesMerge3RawSpec, hmb, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm, hsp]
    apply SepWP.exists_elim; intro cap2'; apply SepWP.exists_elim; intro ptr2'
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hcap2'⟩
    apply SepWP.fold (skipBelow3_bytesMerge3_entails s0.sp 97 (by decide) (by decide)) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    have hcap_fold :
        vecU8At A x.msgPtr cap1 ptr1 m.rootKey ∗ vecU8At A (x.msgPtr + 24#64) cap2' ptr2' v ⊢
          authenticatorPBCapAt A x.msgPtr rest'.length { m with macKey := v } := by
      unfold authenticatorPBCapAt
      refine sepConj_mono ?_ ?_
      · refine Entails.trans (Entails.pure_right hcap1' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap1 (Entails.sepExists_right ptr1 (Entails.refl _))
      · refine Entails.trans (Entails.pure_right hcap2' (Entails.refl _)) ?_
        exact Entails.sepExists_right cap2' (Entails.sepExists_right ptr2' (Entails.refl _))
    apply SepWP.fold hcap_fold (by sep_focus)
    wp_steps
    wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' :=
      authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with macKey := v } x.bs rest')
      (Entails.of_eq (by dsimp only [authLoopPre]; ac_rfl))
    exact hcont v rest' _ hmb
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
      (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-! ## Loop Exit, Key Decode, and Main Loop Induction -/

theorem auth_loop_le_exit_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hle_lim : cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : limit < 2 ^ 63)
    (hres_cur : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = limit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hcur_eq_drop : x.bs.drop (x.bs.length - limit) = cur := by rw [← heq_lim]; exact hcur_suf.symm
    have hsome : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        some (m, cur) := by
      rw [hres_cur, mergeLoopBin_eq_limit _ _ _ _ _ _ heq_lim, Option.map_some, hcur_eq_drop]
    apply SepWPp.of_sepWP_ret
    unfold WppPost authMergeSpec
    simp only [hsome, authMergeStack, stackAt_skipField3 _ 97 (by decide), authLoopPre,
      sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps
    wp_done
  · have hlt_lim : cur.length < limit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt_lim, Option.map_none]
    have hfrom_exit := @auth_from_err_exit_cl_placed _ A H hFromCall x R s0
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinv
    conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_split_96 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0
    wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_reach; intro hinv'
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
       by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
       by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28],
       by simp only [arm64_norm, hvregs]⟩ hinv'

theorem auth_decode_key_step_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 s : State}
    {m : ProtoAuthenticator} {cur : List (BitVec 8)} {limit : Nat}
    (hgt_lim : ¬ cur.length ≤ limit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hres_cur : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
      (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
        (fun m' => (m', x.bs.drop (x.bs.length - limit))))
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_295).base + 212#64 →
      s'.status = .Running → s'.sp = s0.sp - 96#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s'
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (authMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_295).base + 160#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 96#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hcs : HighCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
      (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ := hcs
  obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have herr0_exit := @auth_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @auth_from_err_exit_cl_placed _ A H hFromCall x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
  conv => arg 4; rw [authLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, skipBelow3_leaf s0.sp 97 (by decide)]
  simp only [sepConj_assoc]
  wp_steps
  wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_295).base + 180#64) hVarintCall hinv
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [hres_cur, mergeLoopBin_of_decodeVarint_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd, Option.map_none]
    apply SepWPp.of_sepWP (mid := (blkPl_295).base + 116#64)
    conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
    wp_steps
    wp_reach
    apply SepWPp.weaken_pre (P' :=
      decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
        skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm1
      ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
       by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
       by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
       by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
        rw [hres_cur, mergeLoopBin_of_key_ge protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge, Option.map_none]
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
      conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
      wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 := pointsTo64_memRegion32_entails_40 s0.sp key
      rw [← bv_sub_add_lit s0.sp 96 8] at h40
      apply SepWP.fold h40 (by sep_focus)
      wp_reach; intro hinvm'
      apply SepWPp.weaken_pre (P' :=
        ((s0.sp - 96#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 88#64) 40 ∗
          skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [authErrFrame]; sep_entail)
      exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
         by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
         by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
         by simp only [arm64_norm, hvregs_m]⟩ hinvm'
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          rw [hres_cur, mergeLoopBin_of_wt_none protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt, Option.map_none]
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
        conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split2 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 := pointsTo64_memRegion32_entails_40 s0.sp (key &&& 7#64)
        rw [← bv_sub_add_lit s0.sp 96 8] at h40
        apply SepWP.fold h40 (by sep_focus)
        wp_reach; intro hinvm'
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_err1) ∗ memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [authErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
           by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
           by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
           by simp only [arm64_norm, hvregs_m]⟩ hinvm'
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            rw [hres_cur, mergeLoopBin_of_tag_zero protoPrefixStep_protoAuthenticator_mergeField hgt_lim hd hk_ge hwt hitag0, Option.map_none]
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_split_96 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0
          wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach; intro hinvm'
          apply SepWPp.weaken_pre (P' :=
            ((s0.sp - 96#64) ↦₆₄ v_err0) ∗ memRegion (s0.sp - 88#64) 40 ∗
              skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [authErrFrame]; sep_entail)
          exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm'
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h
            have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1
            omega
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 212#64) hinvm
          conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps
          wp_reach; intro hinvm
          apply SepWPp.weaken_pre (P' := authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [authLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
            (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt])
            (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m])
            (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            ⟨by simp only [arm64_norm, hx23_m], by simp only [arm64_norm, hx24_m],
             by simp only [arm64_norm, hx25_m], by simp only [arm64_norm, hx26_m],
             by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m],
             by simp only [arm64_norm, hvregs_m]⟩ hinvm

theorem auth_loop_ok_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    {x : AuthMergeGhost} {R : SepProp} {s0 : State} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : limit < 2 ^ 63) :
    ∀ (n : Nat) (m : ProtoAuthenticator) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
        (mergeLoopBin ProtoAuthenticator.mergeField (cur.length - limit) m cur limit 96).map
          (fun m' => (m', x.bs.drop (x.bs.length - limit))) →
      s.pc = (blkPl_295).base + 160#64 →
      s.status = .Running → s.sp = s0.sp - 96#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      HighCalleeSaved s0 s → LibsignalCodeRoLoaded lsmpl s.mem →
      SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s
        (authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (authMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest iwt} => @auth_tag1_step_cl_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have htag2_step := fun {s m rest iwt} => @auth_tag2_step_cl_placed _ A H hPushCall hBytesCall x R s0 s m rest iwt limit
  have hskip_step := fun {s m rest tag iwt} => @auth_skip_step_cl_placed _ A H hSkipCall x R s0 s m rest iwt tag limit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    exact auth_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres_cur hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
    by_cases hle_lim : cur.length ≤ limit
    · exact auth_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        hres_cur hpc hrun hsp htr hx21 hx22 hcs hinv
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine auth_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hres_cur ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hcs hinv
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hcs' hinv'
      obtain ⟨hx23', hx24', hx25', hx26', hx27', hx28', hvregs'⟩ := hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
      have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
      have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 96)
        protoPrefixStep_protoAuthenticator_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hloop_ok
        rw [protoAuthenticator_mergeField_tag1] at hloop_ok
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 252#64) hinv'
        wp_steps; wp_reach; intro hinv'
        have hnone_mb : mergeBytes iwt rest = none →
            (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
          intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
        refine htag1_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
          (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
          (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
          (by simp only [arm64_norm, hx0'])
          (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
          (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
          ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
           by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
           by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
           by simp only [arm64_norm, hvregs']⟩ hinv'
        have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
        have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
        have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with rootKey := v } rest' limit 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
          simp only [hres_cur, hloop_ok, hmb, Option.map_some]
        exact ih { m with rootKey := v } rest' s'' (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
          hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hloop_ok
          rw [protoAuthenticator_mergeField_tag2] at hloop_ok
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 228#64) hinv'
          wp_steps; wp_reach; intro hinv'
          have hnone_mb : mergeBytes iwt rest = none →
              (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hmb; simp only [hres_cur, hloop_ok, hmb, Option.map_none]
          refine htag2_step hsp_align hrest_le hrest_lt hrest_suf hnone_mb
            (fun v rest' s'' hmb hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv'' => ?_)
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun'])
            (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr'])
            (by simp only [arm64_norm, hx0'])
            (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22'])
            ⟨by simp only [arm64_norm, hx23'], by simp only [arm64_norm, hx24'],
             by simp only [arm64_norm, hx25'], by simp only [arm64_norm, hx26'],
             by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'],
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_lt : rest'.length < rest.length := mergeBytes_length hmb
          have hrest'_le_rest : rest'.length ≤ rest.length := Nat.le_of_lt hrest'_lt
          have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) { m with macKey := v } rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            simp only [hres_cur, hloop_ok, hmb, Option.map_some]
          exact ih { m with macKey := v } rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest (mergeBytes_suffix hmb))
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
          apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 140#64) hinv'
          wp_steps; wp_reach; intro hinv'
          have hnone_sf : skipField (2 * rest.length + 2) 96 (key.toNat / 8) iwt rest = none →
              (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
            intro hsf; rw [hres_cur, hloop_ok, hsf]; rfl
          refine hskip_step hsp_align hrest_le hrest_lt hrest_suf hitag_lt hnone_sf
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
             by simp only [arm64_norm, hvregs']⟩ hinv'
          have hrest'_le_rest : rest'.length ≤ rest.length :=
            (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
          have hres_next : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption =
              (mergeLoopBin ProtoAuthenticator.mergeField (rest'.length - limit) m rest' limit 96).map
                (fun m' => (m', x.bs.drop (x.bs.length - limit))) := by
            rw [hres_cur, hloop_ok, hsf]; rfl
          exact ih m rest' s'' (by omega) (by omega)
            (suffix_trans hrest_le hrest_suf hrest'_le_rest
              ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
            hres_next hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hcs'' hinv''

/-! ## Entry Prelude and Top-Level Contracts -/

theorem auth_merge_cl_placed_ok_of_cro_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp authMergeSpec
  wpp_init x s0
  apply SepWPp.elim_lscroProp; intro hinv0
  replace hpc : s0.pc = (blkPl_295).base := hpc
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp ((blkPC_295).rebase (blkPl_295).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (authMergeSpec A) x R s0) (WppPanic R s0)
  have herr0_exit := @auth_err0_ret_exit_placed _ A H x R s0
  have hfrom_exit := @auth_from_err_exit_cl_placed _ A H hFromCall x R s0
  have hloop := @auth_loop_ok_cl_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall x R s0
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), skipBelow3_leaf s0.sp 97 (by decide)]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    wp_steps
    wp_reach; intro hinv0
    refine SepWPp.call_frame_lscro (spec := decodeVarint2Spec A) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_295).base + 48#64) hVarintCall hinv0
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl)
      h (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm
    simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hfp_m, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hfp_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption = none := by
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      rw [hwt_ld] at herr0_exit
      apply SepWPp.of_sepWP (mid := (blkPl_295).base + 116#64)
      conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
      apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps
      wp_reach
      apply SepWPp.weaken_pre (P' :=
        decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 96#64) 48 ∗
          skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [authErrFrame]; sep_entail)
      exact herr0_exit hnone hsp_align
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
        have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption = none := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'
            injection hdv0' with hpair; injection hpair with hlen hr0; subst hlen hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        rw [hwt_ld] at hfrom_exit
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinvm
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_split_96 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
        apply SepWP.exists_elim; intro v_stk0
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach; intro hinvm'
        apply SepWPp.weaken_pre (P' :=
          ((s0.sp - 96#64) ↦₆₄ v_stk0) ∗ memRegion (s0.sp - 88#64) 40 ∗
            skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [authErrFrame]; sep_entail)
        exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
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
        have hres0 : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto .lengthDelimited) x.msg x.bs 97).toOption =
            (mergeLoopBin ProtoAuthenticator.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 96).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
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
        rw [hwt_ld] at hloop
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 160#64) hinvm
        conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm]
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (skipBelow3_leaf_entails s0.sp 97 (by decide)) (by sep_focus)
        apply SepWP.fold (authenticatorPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' :=
          authLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [authLoopPre]; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]; sep_entail)
        exact hloop hsp_align h hlim_lt
          rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf hres0
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
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [← hbne1]; congr 2; bv_bits
    have hnone : (Proto.mergeMessage ProtoAuthenticator.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 97).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_protoAuthenticator_mergeField]
      cases hxwt : x.wt <;> first | exact absurd hxwt hwt_ld | rfl
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_295).base + 100#64) hinv0
    conv => arg 4; rw [authMergeStack, stackAt_skipField3 s0.sp 97 (by decide), sliceCursorAt, memRegion_48_wtErr96 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v19; apply SepWP.exists_elim; intro v20
    apply SepWP.exists_elim; intro v21; apply SepWP.exists_elim; intro v22
    apply SepWP.exists_elim; intro v_lr; apply SepWP.exists_elim; intro v_fp
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0
    apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr96_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (authenticatorPBCapAt_entails_authenticatorPBAt A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach; intro hinv0'
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 96#64) ↦₆₄ v_wt0) ∗ memRegion (s0.sp - 88#64) 40 ∗
        skipBelow3 s0.sp 97 ∗ authErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [authErrFrame]; sep_entail)
    exact hfrom_exit hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm]⟩ hinv0'

/-- Contract-parameterized code-loaded `[LibsignalPlacement]` verification of `Authenticator::merge` (Block `295`). -/
theorem auth_merge_cl_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H) (blkPl_295).base (withLsCodeRoLoaded lsmpl (authMergeSpec A)) :=
  auth_merge_cl_placed_ok_of_cro_contracts
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hFromCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hPushCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hVarintCall)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hSkipCall) hBytesCall

end LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlaced
