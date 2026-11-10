/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.DefsClPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Exit & Tag-Step Lemmas for `PolynomialEncoder::merge` (Block `297`)

Proves the `[LibsignalPlacement]` shared error-exit, unknown-tag skip, and per-tag (`tag1`–`tag3`)
step lemmas for `PolynomialEncoder::merge` on Block `297` with `withLsCodeRoLoaded lsmpl` callees.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Prost.BytesMerge CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Placed shared exit from `+0x070` (`(blkPl_297).base + 112#64`) with `withLsCodeRoLoaded` on `DecodeError::from` (`261`). -/
theorem polyEncoder_from_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {w : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hw : KindNoHeap w) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 112#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ w) ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗
        polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyEncoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := (s0.sp - 128#64, w))
    (ret_pc := (blkPl_297).base + 120#64) hFromCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
    hw (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyEncoderMergeSpec
  simp only [decodeErrorFromSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  apply SepWP.fold (memRegion8_memRegion40_entails_48_160 s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_zero_entails_le1 A _) (by sep_focus)
  apply SepWP.fold (protoPolynomialEncoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus); wp_done

/-- Placed shared exit from `+0x344` (`(blkPl_297).base + 836#64`) with `withLsCodeRoLoaded` on `DecodeError::push` (`257`). -/
theorem polyEncoder_push_err_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {err : BitVec 64}
    (hnone : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_297).base + 836#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err 0 ∗
        memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗
        memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 257) hinv
  conv => arg 4; rw [polyBelow_decodeErrorHook s0.sp, polyEncoderErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := (s0.sp - 128#64, err, 0))
    (ret_pc := (blkPl_297).base + 840#64) hPushCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by decide : 0 < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm _; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hspm hx26_m hx27_m hx28_m hvregs_m
  apply SepWPp.of_sepWP_ret; unfold WppPost polyEncoderMergeSpec
  simp only [decodeErrorPushSpec, hnone, polySavedRegsAny, polySavedRegs,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp, hspm]
  apply SepWP.exists_elim; intro v_pad
  apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus)
  wp_steps
  apply SepWP.fold (decodeErrorWith_one_entails_le1 A err) (by sep_focus)
  apply SepWP.fold (protoPolynomialEncoderAt_entails_exists A x.msgPtr m) (by sep_focus)
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus)
  apply SepWP.fold (stackAt_polyMerge_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus); wp_done

/-- Placed step lemma for unknown field tags (`tag ∉ {1, 2, 3}`) at `+0x1d0` (`(blkPl_297).base + 464#64`) with `withLsCodeRoLoaded` on `263`. -/
theorem polyEncoder_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {tag limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_sf : skipField (2 * rest.length + 2) 97 tag iwt rest = none →
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 97 tag iwt rest = some rest' →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_297).base + 464#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have herr0_exit := @polyEncoder_err0_ret_exit_placed _ A H x R s0
  apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 263) hinv
  conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf]; simp only [sepConj_assoc]
  wp_steps; wp_reach; intro hinv
  refine SepWPp.call_frame_lscro (x := ⟨iwt, tag, 97, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_297).base + 476#64) hSkipCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx0, hx1, hx19, setWidth8_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 97 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 97 tag iwt rest with
  | none =>
    have hnone := hnone_of_sf hsf
    apply SepWPp.of_sepWP (mid := (blkPl_297).base + 124#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps; wp_reach
    apply SepWPp.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ memRegion (s0.sp - 128#64) 48 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (Entails.of_eq (by dsimp only [polyEncoderErrFrame]; ac_rfl))
    exact herr0_exit hnone hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm]) hsm0 ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest') (Entails.of_eq (by dsimp only [polyEncoderLoopPre]; ac_rfl))
    exact hcont rest' _ hsf
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
      (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Placed step lemma for tag 1 (`idx : u32` at `msgPtr + 48#64`) at `+0x1b0` (`(blkPl_297).base + 432#64`) with `withLsCodeRoLoaded` callees. -/
theorem polyEncoder_tag1_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_wt : iwt ≠ .varint → (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hnone_of_dv : iwt = .varint → decodeVarint rest = none → (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : BitVec 64) (rest' : List (BitVec 8)) (s' : State),
      iwt = .varint → decodeVarint rest = some (v, rest') →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 → PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with idx := v.truncate 32 } x.bs rest')
        (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_297).base + 432#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyEncoder_push_err_exit_cl_placed _ A H hPushCall x R s0
  by_cases hiwt : iwt = .varint
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 291) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, polyBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_297).base + 444#64) hVarintCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl) hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv : decodeVarint rest with
    | none =>
      have hnone := hnone_of_dv rfl hdv
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 1#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
    | some p =>
      rcases p with ⟨v, rest'⟩
      have hrest'_le : rest'.length ≤ rest.length := Nat.le_of_lt (decodeVarint_length hdv)
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 164#64) hinvm
      (conv => arg 4; simp only [decodeVarint2Spec, hdv, protoPolynomialEncoderAt, protoPolynomialEncoderIdxOff, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (polyBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus); wp_steps; wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with idx := v.truncate 32 } x.bs rest') (by dsimp only [polyEncoderLoopPre, protoPolynomialEncoderAt, protoPolynomialEncoderIdxOff]; sep_entail)
      exact hcont v rest' _ rfl hdv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
        (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_wt hiwt; have hcbnz := iwt_cbnz_true_of_ne_varint hiwt
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_297).base + 604#64) hFromCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl)
      (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm, hspm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Placed step lemma for tag 2 (`pts : Vec<Vec<u8>>` at `msgPtr`) at `+0x150` (`(blkPl_297).base + 336#64`) with `withLsCodeRoLoaded` callees. -/
theorem polyEncoder_tag2_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpts_bound : m.pts.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with pts := m.pts ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_297).base + 336#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyEncoder_push_err_exit_cl_placed _ A H hPushCall x R s0; have hcopy := @polyEncoder_tag2_copy_step_placed _ A H x R s0 m
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2; apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A s0.sp).symm) (by sep_focus); wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_297).base + 364#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19]); rfl)
      (⟨by omega, Or.inl rfl⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk 0#64 rest.length) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, vecU8At_zero_eq_cells A s0.sp, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus); wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm0 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
    | some p =>
      rcases p with ⟨v, rest'⟩; have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      (conv => arg 4; rw [protoPolynomialEncoderAt_unfold_pts]; simp only [bytesMerge3RawSpec, hmb, List.nil_append, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr; apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      apply SepWPp.pure_elim; rintro ⟨⟨htrm, hsm0, _⟩, ⟨hlen_le, hcap_bound, hptr_ne⟩⟩
      by_cases hcap_eq : m.pts.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.pts.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A cap ptr m.pts hcap_eq) (by sep_focus)
        (conv => arg 4; rw [polyBelow_extHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro pins; apply SepWP.pure_elim; rintro ⟨hpins_len, hbytes_len⟩; wp_steps; wp_reach; intro hinvm
        refine SepWPp.call_frame_lscro (x := ⟨x.msgPtr, cap, ptr, vecU8ArrayBytes pins m.pts⟩)
          (ret_pc := (blkPl_297).base + 392#64) hGrowCall hinvm (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          (by conv => lhs; dsimp only [growOneVecU8Spec]; simp only [arm64_norm, hspm, hx20_m])
          (And.intro hbytes_len (And.intro hptr_ne (by omega : max (2 * cap.toNat) 4 * 24 ≤ 9223372036854775800))) (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m] at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        (conv => arg 4; simp only [growOneVecU8Spec, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hspm])
        apply SepWPp.exists_elim; intro p'; apply SepWPp.pure_elim; rintro ⟨htrm2, hp'_ne, _⟩
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.pts.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        apply SepWPp.fold (grow_post_entails_ready A cap p' pins m.pts hcap_eq hpins_len hgrow_bound) (by sep_focus)
        apply SepWPp.fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ newCapVecU8 cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ p') ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live p' ((newCapVecU8 cap).toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 p' m.pts ∗
          memRegion (p' + BitVec.ofNat 64 (m.pts.length * 24)) (((newCapVecU8 cap).toNat - m.pts.length) * 24) ∗
          vecVecU8At A (x.msgPtr + protoPolynomialEncoderPolysOff) m.polys ∗
          ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
          memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt_new hbound_new hp'_ne (fun s' => hcont v rest' s' hmb)
          hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr)) hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2
      · have hlt : m.pts.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.pts.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.pts.length < 0 at hlt; omega
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 392#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          (x.msgPtr ↦₆₄ cap) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr) ∗
          ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 m.pts.length) ∗
          A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.pts ∗
          memRegion (ptr + BitVec.ofNat 64 (m.pts.length * 24)) ((cap.toNat - m.pts.length) * 24) ∗
          vecVecU8At A (x.msgPtr + protoPolynomialEncoderPolysOff) m.polys ∗
          ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
          memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt hcap_bound hptr_ne (fun s' => hcont v rest' s' hmb)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_297).base + 664#64) hFromCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

/-- Placed step lemma for tag 3 (`polys : Vec<Vec<u8>>` at `msgPtr + 24#64`) at `+0x0f0` (`(blkPl_297).base + 240#64`) with `withLsCodeRoLoaded` callees. -/
theorem polyEncoder_tag3_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hBytesCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hGrowCall : subroutine_ok ((blkPC_297).rebase (blkPl_297).base H) (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8Spec A)))
    {x : PolyEncoderMergeGhost} {R : SepProp} {s0 s : State} {m : PolynomialEncoder} {rest : List (BitVec 8)} {iwt : WireType} {limit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hpolys_bound : m.polys.length + rest.length < 2 ^ 56) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_mb : mergeBytes iwt rest = none →
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 98).toOption = none)
    (hcont : ∀ (v : List (BitVec 8)) (rest' : List (BitVec 8)) (s' : State),
      mergeBytes iwt rest = some (v, rest') →
      s'.pc = (blkPl_297).base + 164#64 →
      s'.status = .Running → s'.sp = s0.sp - 160#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 24#64 →
      PolyCalleeSaved s0 s' → LibsignalCodeRoLoaded lsmpl s'.mem →
      SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s'
        (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with polys := m.polys ++ [v] } x.bs rest')
        (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_297).base + 240#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 160#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 limit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 24#64)
    (hcs : PolyCalleeSaved s0 s) (hinv : LibsignalCodeRoLoaded lsmpl s.mem) :
    SepWPp ((blkPC_297).rebase (blkPl_297).base H) (s0.readReg64 Reg.lr) s
      (polyEncoderLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (polyEncoderMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @polyEncoder_push_err_exit_cl_placed _ A H hPushCall x R s0; have hcopy := @polyEncoder_tag3_copy_step_placed _ A H x R s0 m
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt; dsimp [WireType.toNat] at hx0
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 290) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, memRegion_32_cells160 s0.sp, polyBelow_bytesMerge3 s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk3; apply SepWP.exists_elim; intro v_stk2; apply SepWP.exists_elim; intro v_stk1; apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (Entails.of_eq (vecU8At_zero_eq_cells A s0.sp).symm) (by sep_focus); wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := ⟨.lengthDelimited, s0.sp - 152#64, 0#64, 1#64, [], x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_297).base + 268#64) hBytesCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by (conv => lhs; dsimp only [bytesMerge3RawSpec]; simp only [arm64_norm, hsp, hx0, hx19]); rfl)
      (⟨by omega, Or.inl rfl⟩ : rest.length < 2 ^ 63 ∧ BytesMergeCapOk 0#64 rest.length) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hmb : mergeBytes .lengthDelimited rest with
    | none =>
      have hnone := hnone_of_mb hmb
      apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
      (conv => arg 4; simp only [bytesMerge3RawSpec, hmb, vecU8At_zero_eq_cells A s0.sp, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.exists_elim; intro v_err0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
      have hcbnz_err : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
      apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_steps
      apply SepWP.fold (cells160_entails_memRegion32 s0.sp v_stk0 0#64 1#64 0#64) (by sep_focus); wp_reach; intro hinvm
      apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
      exact hpush_exit hnone hsm0 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
    | some p =>
      rcases p with ⟨v, rest'⟩; have hrest'_le : rest'.length ≤ rest.length := mergeBytes_length hmb
      (conv => arg 4; rw [protoPolynomialEncoderAt_unfold_polys]; simp only [bytesMerge3RawSpec, hmb, List.nil_append, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
      apply SepWPp.exists_elim; intro cap; apply SepWPp.exists_elim; intro ptr; apply SepWPp.exists_elim; intro cap_e; apply SepWPp.exists_elim; intro ptr_e
      apply SepWPp.pure_elim; rintro ⟨⟨htrm, hsm0, _⟩, ⟨hlen_le, hcap_bound, hptr_ne⟩⟩
      by_cases hcap_eq : m.polys.length = cap.toNat
      · have hbne : (BitVec.ofNat 64 m.polys.length != cap) = false := len_eq_cap_bne_false hcap_eq
        have hgrow_bound : max (2 * cap.toNat) 4 * 24 + 8 ≤ 2 ^ 63 := by omega
        apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 621) hinvm
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        apply SepWP.fold (vecBuf_vecU8_entails_grow_pre A cap ptr m.polys hcap_eq) (by sep_focus)
        (conv => arg 4; rw [polyBelow_extHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
        apply SepWP.exists_elim; intro pins; apply SepWP.pure_elim; rintro ⟨hpins_len, hbytes_len⟩; wp_steps; wp_reach; intro hinvm
        refine SepWPp.call_frame_lscro (x := ⟨x.msgPtr + 24#64, cap, ptr, vecU8ArrayBytes pins m.polys⟩)
          (ret_pc := (blkPl_297).base + 296#64) hGrowCall hinvm (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
          (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
          (by conv => lhs; dsimp only [growOneVecU8Spec]; simp only [arm64_norm, hspm, hx20_m, bv64_add24_add8])
          (And.intro hbytes_len (And.intro hptr_ne (by omega : max (2 * cap.toNat) 4 * 24 ≤ 9223372036854775800))) (by sep_focus)
          (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htrm, htr]) hpan) ?_
        intro sm2 hpcm2 hrunm2 hspm2 hcsm2 hinvm2; simp only [CalleeSavedPreserved] at hcsm2
        obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩ := hcsm2
        simp (config := { decide := true }) only [arm64_norm, hspm, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hx27_m, hx28_m, hvregs_m] at hpcm2 hrunm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
        (conv => arg 4; simp only [growOneVecU8Spec, bv64_add24_add8, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hspm])
        apply SepWPp.exists_elim; intro p'; apply SepWPp.pure_elim; rintro ⟨htrm2, hp'_ne, _⟩
        have hnew_toNat : (newCapVecU8 cap).toNat = max (2 * cap.toNat) 4 := by
          unfold newCapVecU8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hlt_new : m.polys.length < (newCapVecU8 cap).toNat := by rw [hnew_toNat]; omega
        have hbound_new : (newCapVecU8 cap).toNat * 24 < 2 ^ 63 := by rw [hnew_toNat]; omega
        apply SepWPp.fold (grow_post_entails_ready A cap p' pins m.polys hcap_eq hpins_len hgrow_bound) (by sep_focus)
        apply SepWPp.fold (polyBelow_extHook_entails s0.sp) (by sep_focus)
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          vecVecU8At A x.msgPtr m.pts ∗
          ((x.msgPtr + 24#64) ↦₆₄ newCapVecU8 cap) ∗ ((x.msgPtr + 32#64) ↦₆₄ p') ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
          A.live p' ((newCapVecU8 cap).toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 p' m.polys ∗
          memRegion (p' + BitVec.ofNat 64 (m.polys.length * 24)) (((newCapVecU8 cap).toNat - m.polys.length) * 24) ∗
          ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
          memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt_new hbound_new hp'_ne (fun s' => hcont v rest' s' hmb)
          hpcm2 hrunm2 hspm2 (htrm2.trans (htrm.trans htr)) hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2
          (hx25_2.trans (by rw [hcap_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq])) ⟨hx26_2, hx27_2, hx28_2, hvregs_2⟩ hinvm2
      · have hlt : m.polys.length < cap.toNat := Nat.lt_of_le_of_ne hlen_le hcap_eq
        have hbne : (BitVec.ofNat 64 m.polys.length != cap) = true := len_lt_cap_bne_true hlt
        have hcap_ne0 : cap ≠ 0 := by intro h0; subst h0; change m.polys.length < 0 at hlt; omega
        apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 296#64) hinvm
        (conv => arg 4; simp only [hcap_ne0, ↓reduceIte, bv64_add24_add8, sepConj_assoc])
        apply SepWP.fold (polyBelow_bytesMerge3_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
        wp_steps; wp_reach; intro hinvm
        apply SepWPp.weaken_pre (P' := ((s0.sp - 160#64) ↦₆₄ v_stk0) ∗ vecU8At A (s0.sp - 152#64) cap_e ptr_e v ∗
          vecVecU8At A x.msgPtr m.pts ∗
          ((x.msgPtr + 24#64) ↦₆₄ cap) ∗ ((x.msgPtr + 32#64) ↦₆₄ ptr) ∗
          ((x.msgPtr + 40#64) ↦₆₄ BitVec.ofNat 64 m.polys.length) ∗
          A.live ptr (cap.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 ptr m.polys ∗
          memRegion (ptr + BitVec.ofNat 64 (m.polys.length * 24)) ((cap.toNat - m.polys.length) * 24) ∗
          ((x.msgPtr + protoPolynomialEncoderIdxOff) ↦₃₂ m.idx) ∗
          memRegion (x.msgPtr + protoPolynomialEncoderPadOff) protoPolynomialEncoderPadSize ∗
          stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗
          polySavedRegsAny s0.sp s0 ∗ (x.bufRef ↦₆₄ x.slot) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest' ∗ A.pool) (by sep_entail)
        exact hcopy hsp_align hlt hcap_bound hptr_ne (fun s' => hcont v rest' s' hmb)
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm
  · have hnone := hnone_of_mb (mergeBytes_eq_none_of_ne_len hiwt)
    obtain ⟨hbne2_64, hbne2_32⟩ := iwt_bne_two_true_of_ne_len hiwt
    apply SepWPp.of_sepWP_lscro (mid := lsmpl.base 261) hinv
    conv => arg 4; rw [polyEncoderLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp, polyBelow_decodeErrorHook s0.sp]; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); wp_reach; intro hinv
    refine SepWPp.call_frame_lscro (x := (s0.sp - 128#64, 0x8000000000000006#64))
      (ret_pc := (blkPl_297).base + 700#64) hFromCall hinv (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeErrorFromSpec]; simp only [arm64_norm, hsp]; rfl) (by decide : KindNoHeap 0x8000000000000006#64) (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm hinvm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨_, _, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx26_m hx27_m hx28_m hvregs_m
    apply SepWPp.of_sepWP_lscro (mid := (blkPl_297).base + 836#64) hinvm
    (conv => arg 4; simp only [decodeErrorFromSpec, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨hve_ne, htrm⟩
    apply SepWP.fold (polyBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps; wp_reach; intro hinvm
    apply SepWPp.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 160#64) polyBelowStack ∗ memRegion (s0.sp - 160#64) 32 ∗ polyEncoderErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs) (by dsimp only [polyEncoderErrFrame]; sep_entail)
    exact hpush_exit hnone hve_ne hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩ hinvm

end CryptoVerification.SpqrV1.Prost.MessageMerge
