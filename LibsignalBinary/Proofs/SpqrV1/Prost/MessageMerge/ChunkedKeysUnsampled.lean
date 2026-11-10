/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampledUc
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Verification of `Chunked.KeysUnsampled::merge` (`0x50854`, Block `305`)

Proves `prost::encoding::message::merge::<spqr::proto::pq_ratchet::v1_state::chunked::KeysUnsampled, &mut &[u8]>`
against `(chunkedKeysUnsampledMergeSpec A).inImage img` and its `[LibsignalPlacement]` counterpart
on Block `305`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageMerge

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Helper Lemmas for `cmn #2` and Wire-Type Checks -/

private theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; have h1 := congrArg BitVec.toNat heq; revert h1; bv_omega

private theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  simp only [bne, cap_add_two_beq_zero_false h, Bool.not_false]

private theorem iwt64_beq_two_of_ne_ld {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> simp_all [WireType.toNat]

private theorem setWidth8_zext64_trunc32_ofNat64_wt (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) =
      BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

/-! ## 2. Outer Loop Step Lemmas -/

/-- Outer loop `skip_field` step at `+0x0a8` (`entry + 168#64`) for unknown tags (`tag ≠ 1`, `depth' = 98`). -/
theorem chunkedKeysUnsampled_skip_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffb320#64) (skipField3Spec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit img A H x R s0 m
  chunkedKeysUnsampledMerge_fetches img.base H 168 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffb320#64)
  conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField98 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 184#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx8, hx1, hx19, setWidth8_zext64_trunc32_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPpIn.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpIn.of_sepWP (mid := entry + 188#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [chunkedKeysUnsampledLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Prepares `chunkedKeysUnsampledPBCapAt` at `+0x100` (`entry + 256#64`) into `chunkedKeysUnsampledUcLoopPre` at `+0x114` (`entry + 276#64`). -/
theorem chunkedKeysUnsampled_uc_init {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 276#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr (m.uc.getD default) x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; chunkedKeysUnsampledMerge_fetches img.base H 256 20
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  rcases huc : m.uc with _ | uc
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpIn.of_sepWP (mid := entry + 276#64)
    conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt, memRegion_48_split_40_8 x.msgPtr]
    simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v48; wp_steps
    have hdef : (x.msgPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 8#64) 40 ∗ ((x.msgPtr + 48#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A x.msgPtr rest.length (default : V1State.Unchunked.KeysUnsampled).epoch (default : V1State.Unchunked.KeysUnsampled).auth :=
      default_unchunked2_entails_cap A x.msgPtr rest.length
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr default x.bs rest)
      (by dsimp only [chunkedKeysUnsampledUcLoopPre]; sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    rcases hauth : uc.auth with _ | auth
    · apply SepWPpIn.of_sepWP (mid := entry + 276#64)
      conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [noneCap, sepConj_assoc]; wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (by dsimp only [chunkedKeysUnsampledUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt, noneCap]; sep_entail)
      exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
    · have hvec_swap : ∀ (v cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8At A v cap ptr bs = vecU8Buf A cap ptr bs ∗ vecHeader v cap ptr (BitVec.ofNat 64 bs.length) := by
        intro v cap ptr bs; unfold vecU8At vecU8Buf; ac_rfl
      apply SepWPpIn.of_sepWP (mid := entry + 276#64)
      conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt, authenticatorPBCapAt]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik; apply SepWP.pure_elim; intro hcap_ik
      conv => arg 4; rw [hvec_swap x.msgPtr cap_ik ptr_ik auth.rootKey, vecU8Buf, vecHeader]
      simp only [sepConj_assoc]; apply SepWP.pure_elim; intro hbuf_ok
      have hcmn1 := cap_add_two_beq_zero_false hbuf_ok.2.1; have hcmn2 := cap_add_two_bne_zero_true hbuf_ok.2.1
      wp_steps; wp_reach
      have hrestore :
          ((if cap_ik = 0 then emp else A.live ptr_ik cap_ik.toNat 1 ∗ (ptr_ik ↦ₛ auth.rootKey) ∗ memRegion (ptr_ik + BitVec.ofNat 64 auth.rootKey.length) (cap_ik.toNat - auth.rootKey.length)) ∗
            (x.msgPtr ↦₆₄ cap_ik) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr_ik) ∗
            ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length)) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.macKey) ⊢
          authenticatorPBCapAt A x.msgPtr rest.length auth := by
        unfold authenticatorPBCapAt; refine sepConj_mono_left ?_
        refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
        rw [pure_sepConj_of_true hcap_ik, hvec_swap, vecU8Buf, vecHeader, pure_sepConj_of_true hbuf_ok]; exact Entails.of_eq (by ac_rfl)
      apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (by dsimp only [chunkedKeysUnsampledUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt]; simpa only [sepConj_assoc, arm64_norm] using sepConj_mono_left hrestore)
      exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩

/-- Outer loop tag 1 (`uc : Option<Unchunked.KeysUnsampled>`) step at `+0x100` (`entry + 256#64`). -/
theorem chunkedKeysUnsampled_tag1_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa254#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffcc78#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffb320#64) (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffd6e4#64) ((authMergeSpec A).inImage img))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.KeysUnsampled) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc' } x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  refine chunkedKeysUnsampled_uc_init ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1
  obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let uc0 : V1State.Unchunked.KeysUnsampled := m.uc.getD default
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedKeysUnsampled_uc_push_exit img A H hPushCall x R s0 { uc := some uc0 }
  have hfrom_push := @chunkedKeysUnsampled_uc_from_push_exit img A H hFromCall hPushCall x R s0 { uc := some uc0 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_uc_loop_ok img A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 outerLimit innerLimit hsp_align hbs_lt hlim_lt
  chunkedKeysUnsampledMerge_fetches img.base H 276 48; chunkedKeysUnsampledMerge_fetches img.base H 692 28
  chunkedKeysUnsampledMerge_fetches img.base H 832 8; chunkedKeysUnsampledMerge_fetches img.base H 600 4
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffcc78#64)
    conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach
    refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 292#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp1, hx19_1]; rfl)
      hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint rest with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        apply hnone_of_uc
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpIn.of_sepWP (mid := entry + 616#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
      have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpIn.of_sepWP (mid := entry + 604#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
            (mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
              (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
        apply SepWPpIn.of_sepWP (mid := entry + 344#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_mono A x.msgPtr uc0.epoch uc0.auth hrest0_le_rest) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc0 x.bs rest0)
          (by dsimp only [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter]; sep_entail)
        exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f => by
            have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
            refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f
            rw [hres0, hml, hr'_eq]; rfl)
          (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply SepWPpIn.of_sepWP (mid := entry + 604#64)
    conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, htr1])
      ⟨by simp only [arm64_norm, hx26_1], by simp only [arm64_norm, hx27_1], by simp only [arm64_norm, hx28_1], by simp only [arm64_norm, hvregs_1]⟩

/-- Outer loop exit at `+0x0bc` (`entry + 188#64`) when `cur.length ≤ outerLimit`. -/
theorem chunkedKeysUnsampled_loop_le_exit {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64) (decodeErrorFromSpec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < outerLimit →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    chunkedKeysUnsampledMerge_fetches img.base H 188 12; chunkedKeysUnsampledMerge_fetches img.base H 512 12
    chunkedKeysUnsampledMerge_fetches img.base H 128 28
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP_ret; unfold WppPost chunkedKeysUnsampledMergeSpec
    simp only [hsome, chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, polySavedRegsAny, polySavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl9_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @chunkedKeysUnsampled_from_err_exit img A H hFromCall x R s0 m
    chunkedKeysUnsampledMerge_fetches img.base H 188 12; chunkedKeysUnsampledMerge_fetches img.base H 512 4
    chunkedKeysUnsampledMerge_fetches img.base H 676 16; chunkedKeysUnsampledMerge_fetches img.base H 88 8
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
    apply SepWPpIn.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Outer loop key-decode step at `+0x0bc` (`entry + 188#64`) when `¬ cur.length ≤ outerLimit`. -/
theorem chunkedKeysUnsampled_decode_key_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffcc78#64) (decodeVarint2Spec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 248#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit img A H x R s0 m
  have hfrom_err := @chunkedKeysUnsampled_from_err_exit img A H hFromCall x R s0 m
  chunkedKeysUnsampledMerge_fetches img.base H 188 60; chunkedKeysUnsampledMerge_fetches img.base H 544 20
  chunkedKeysUnsampledMerge_fetches img.base H 576 12; chunkedKeysUnsampledMerge_fetches img.base H 660 16
  chunkedKeysUnsampledMerge_fetches img.base H 88 8
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffcc78#64)
  conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 208#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd)
    apply SepWPpIn.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpIn.of_sepWP (mid := entry + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpIn.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpIn.of_sepWP (mid := entry + 120#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpIn.of_sepWP (mid := entry + 248#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [chunkedKeysUnsampledLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Outer loop tag-dispatch step at `+0x0f8` (`entry + 248#64`) branching on `tag = 1` vs `tag ≠ 1`. -/
theorem chunkedKeysUnsampled_dispatch_step {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (htag_lt : tag < 2 ^ 32)
    (htag1 : tag = 1 → ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 256#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hother : tag ≠ 1 → ∀ s' : State,
      s'.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      (s'.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; chunkedKeysUnsampledMerge_fetches img.base H 248 8
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  by_cases h1 : tag = 1
  · subst h1
    apply SepWPpIn.of_sepWP (mid := entry + 256#64); wp_steps; wp_reach
    exact htag1 rfl _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx8]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false h1 htag_lt (by decide : 1 < 2 ^ 32)
    have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
    have hb1_bne1 : (BitVec.ofNat 32 tag != 1#32) = true := by simp only [bne, hb1_1, Bool.not_false]
    have hb1_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) != 1#32) = true := by simp only [bne, hb1_2, Bool.not_false]
    apply SepWPpIn.of_sepWP (mid := entry + 168#64); wp_steps; wp_reach
    exact hother h1 _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx8]) (by simp only [arm64_norm, hx1, sf_truncate32_ofNat64])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

/-- Main outer loop induction at `+0x0bc` (`entry + 188#64`) for `V1State.Chunked.KeysUnsampled.mergeField`. -/
theorem chunkedKeysUnsampled_loop_ok {img : Obj.Image} {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa254#64) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffcc78#64) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffb320#64) (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H) ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffd6e4#64) ((authMergeSpec A).inImage img))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.KeysUnsampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 188#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s →
      SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    exact chunkedKeysUnsampled_loop_le_exit hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedKeysUnsampled_loop_le_exit hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedKeysUnsampled_decode_key_step hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd); have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98) protoPrefixStep_chunked_keysUnsampled_mergeField hle_lim hd hk_ge hwt hitag0
      refine chunkedKeysUnsampled_dispatch_step htag_lt ?_ ?_ hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      · intro htag1 s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        rw [htag1, chunkedKeysUnsampled_mergeField_tag1] at hloop_ok
        refine chunkedKeysUnsampled_tag1_step hFromCall hPushCall hVarintCall hSkipCall hAuthCall
          hsp_align hbs_lt hrest_le hrest_lt hrest_suf
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
        refine chunkedKeysUnsampled_skip_step hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt
          (fun hsf => by rw [hres, hloop_ok, hsf]; rfl)
          (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
        exact ih m rest' s'' (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
          (by rw [hres, hloop_ok, hsf]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs''

/-! ## 3. Top-Level X-World Verification of `chunkedKeysUnsampledMergeSpec` (`0x50854`) -/

/-- Verification of `prost::encoding::message::merge::<V1State.Chunked.KeysUnsampled, &mut &[u8]>` (`0x50854`)
against `(chunkedKeysUnsampledMergeSpec A).inImage img` from offset-form callee contracts. -/
theorem chunked_keys_unsampled_merge_ok_of_contracts {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64)
      (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa254#64)
      (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffcc78#64)
      (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffb320#64)
      (skipField3Spec A))
    (hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffd6e4#64)
      ((authMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName)
      ((chunkedKeysUnsampledMergeSpec A).inImage img) := by
  unfold Spec.inImage chunkedKeysUnsampledMergeSpec
  wpp_init x s0
  have ⟨h_1, h_2, h_3, hbs_lt⟩ :
      (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s0.readReg64 (Reg.gpr 1#5) = x.msgPtr ∧
      s0.readReg64 (Reg.gpr 2#5) = x.bufRef ∧
      x.bs.length < 2 ^ 63 := ⟨h_3, h_4, h_5, h⟩
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName := by
    simpa only [arm64_norm, chunkedKeysUnsampledMerge_fnOff] using hpc
  conv => arg 6; ext sf P_f; rw [sepConj_assoc, satisfies_pure_sepConj]
  change SepWPp (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0)
  have hinv : ImgCallInv img s0 := ⟨‹_›, ‹_›⟩
  revert hinv; change SepWPpIn img (libsignalSessionCode.rebase img.base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit img A H x R s0 x.msg
  have hfrom_err := @chunkedKeysUnsampled_from_err_exit img A H hFromCall x R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_loop_ok img A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 outerLimit hsp_align hbs_lt hlim_lt
  chunkedKeysUnsampledMerge_fetches img.base H 0 124; chunkedKeysUnsampledMerge_fetches img.base H 156 12
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName = entry; examples_hide_fetches
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPpIn.of_sepWP (mid := entry + 0xffffffffffffcc78#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    wp_reach
    refine SepWPpIn.call_frame (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl)
      hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpIn.of_sepWP (mid := entry + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpIn.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpIn.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPpIn.of_sepWP (mid := entry + 188#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpIn.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [chunkedKeysUnsampledLoopPre, sliceCursorAfter]; sep_entail)
        exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply SepWPpIn.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach
    apply SepWPpIn.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

/-- Address-resolved X-world verification of `prost::encoding::message::merge::<V1State.Chunked.KeysUnsampled, &mut &[u8]>` (`0x50854`). -/
theorem chunked_keys_unsampled_merge_ok_of_fnAddr {img : Obj.Image} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFrom : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr skipField3Name)
      (skipField3Spec A))
    (hAuth : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr authMergeName)
      ((authMergeSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName)
      ((chunkedKeysUnsampledMergeSpec A).inImage img) := by
  have hFromCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa54c#64)
      (decodeErrorFromSpec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedKeysUnsampledMergeName) (callee := decodeErrorFromName)]; exact hFrom
  have hPushCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffa254#64)
      (decodeErrorPushSpec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedKeysUnsampledMergeName) (callee := decodeErrorPushName)]; exact hPush
  have hVarintCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffcc78#64)
      (decodeVarint2Spec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedKeysUnsampledMergeName) (callee := Varint.decodeVarint2Name)]; exact hVarint
  have hSkipCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffb320#64)
      (skipField3Spec A) := by
    rw [fnAddr_offset_eq_H (name := chunkedKeysUnsampledMergeName) (callee := skipField3Name)]; exact hSkip
  have hAuthCall : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr chunkedKeysUnsampledMergeName + 0xffffffffffffd6e4#64)
      ((authMergeSpec A).inImage img) := by
    rw [fnAddr_offset_eq_H (name := chunkedKeysUnsampledMergeName) (callee := authMergeName)]; exact hAuth
  exact chunked_keys_unsampled_merge_ok_of_contracts hFromCall hPushCall hVarintCall hSkipCall hAuthCall

/-- `prost::encoding::message::merge::<V1State.Chunked.KeysUnsampled, &mut &[u8]>` (`0x50854`) meets
`(chunkedKeysUnsampledMergeSpec A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def ChunkedKeysUnsampledMergeOkX (img : Obj.Image) (A : RustAlloc) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr chunkedKeysUnsampledMergeName)
    ((chunkedKeysUnsampledMergeSpec A).inImage img)

theorem chunked_keys_unsampled_merge_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hFrom : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A))
    (hPush : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      (decodeErrorPushSpec A))
    (hVarint : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Varint.decodeVarint2Name)
      (decodeVarint2Spec A))
    (hSkip : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr skipField3Name)
      (skipField3Spec A))
    (hAuth : AuthMergeOkX img A ext) :
    ChunkedKeysUnsampledMergeOkX img A ext :=
  chunked_keys_unsampled_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hAuth

/-! ## 4. Relocatable `[LibsignalPlacement]` Outer Loop and Top-Level Verification -/

section Placed

open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option quotPrecheck false in
local notation "entry" => (blkPl_305).base

theorem chunkedKeysUnsampled_skip_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263) (skipField3Spec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_305).base + 168#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
    chunkedInlBelow_skipField98 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := entry + 184#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx8, hx1, hx19, setWidth8_zext64_trunc32_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm0 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := entry + 188#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus)
    apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [chunkedKeysUnsampledLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
      (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m])
      (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedKeysUnsampled_uc_init_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)}
    (hcont : ∀ (s' : State),
      s'.pc = (blkPl_305).base + 276#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s.trace →
      s'.readReg64 (Reg.gpr 8#5) = s.readReg64 (Reg.gpr 8#5) →
      s'.readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5) → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = s.readReg64 (Reg.gpr 21#5) → s'.readReg64 (Reg.gpr 22#5) = s.readReg64 (Reg.gpr 22#5) →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = s.readReg64 (Reg.gpr 24#5) →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr (m.uc.getD default) x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_305).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  rcases huc : m.uc with _ | uc
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    apply SepWPpLscro.of_sepWP (mid := entry + 276#64)
    conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt, memRegion_48_split_40_8 x.msgPtr]
    simp only [noneCap2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v48; wp_steps
    have hdef : (x.msgPtr ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (x.msgPtr + 8#64) 40 ∗ ((x.msgPtr + 48#64) ↦₆₄ 0#64) ⊢
        unchunked2CapAt A x.msgPtr rest.length (default : V1State.Unchunked.KeysUnsampled).epoch (default : V1State.Unchunked.KeysUnsampled).auth :=
      default_unchunked2_entails_cap A x.msgPtr rest.length
    apply SepWP.fold hdef (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr default x.bs rest)
      (by dsimp only [chunkedKeysUnsampledUcLoopPre]; sep_entail)
    exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
      (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
      ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
  · rw [huc] at hcont; dsimp only [Option.getD] at hcont
    rcases hauth : uc.auth with _ | auth
    · apply SepWPpLscro.of_sepWP (mid := entry + 276#64)
      conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt]
      simp only [noneCap, sepConj_assoc]; wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (by dsimp only [chunkedKeysUnsampledUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt, noneCap]; sep_entail)
      exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩
    · have hvec_swap : ∀ (v cap ptr : BitVec 64) (bs : List (BitVec 8)),
          vecU8At A v cap ptr bs = vecU8Buf A cap ptr bs ∗ vecHeader v cap ptr (BitVec.ofNat 64 bs.length) := by
        intro v cap ptr bs; unfold vecU8At vecU8Buf; ac_rfl
      apply SepWPpLscro.of_sepWP (mid := entry + 276#64)
      conv => arg 4; rw [chunkedKeysUnsampledLoopPre, chunkedKeysUnsampledPBCapAt, huc, optKeysUnsampledPBCapAt,
        unchunked2CapAt, hauth, optAuthenticatorPBCapAt, authenticatorPBCapAt]
      simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_elim; intro cap_ik; apply SepWP.exists_elim; intro ptr_ik; apply SepWP.pure_elim; intro hcap_ik
      conv => arg 4; rw [hvec_swap x.msgPtr cap_ik ptr_ik auth.rootKey, vecU8Buf, vecHeader]
      simp only [sepConj_assoc]; apply SepWP.pure_elim; intro hbuf_ok
      have hcmn1 := cap_add_two_beq_zero_false hbuf_ok.2.1; have hcmn2 := cap_add_two_bne_zero_true hbuf_ok.2.1
      wp_steps; wp_reach
      have hrestore :
          ((if cap_ik = 0 then emp else A.live ptr_ik cap_ik.toNat 1 ∗ (ptr_ik ↦ₛ auth.rootKey) ∗ memRegion (ptr_ik + BitVec.ofNat 64 auth.rootKey.length) (cap_ik.toNat - auth.rootKey.length)) ∗
            (x.msgPtr ↦₆₄ cap_ik) ∗ ((x.msgPtr + 8#64) ↦₆₄ ptr_ik) ∗
            ((x.msgPtr + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length)) ∗
            (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ⌜BytesMergeCapOk cap rest.length⌝ ∗ vecU8At A (x.msgPtr + 0x18#64) cap ptr auth.macKey) ⊢
          authenticatorPBCapAt A x.msgPtr rest.length auth := by
        unfold authenticatorPBCapAt; refine sepConj_mono_left ?_
        refine Entails.trans ?_ (Entails.sepExists_intro cap_ik); refine Entails.trans ?_ (Entails.sepExists_intro ptr_ik)
        rw [pure_sepConj_of_true hcap_ik, hvec_swap, vecU8Buf, vecHeader, pure_sepConj_of_true hbuf_ok]; exact Entails.of_eq (by ac_rfl)
      apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc x.bs rest)
        (by dsimp only [chunkedKeysUnsampledUcLoopPre, unchunked2CapAt]; rw [hauth, optAuthenticatorPBCapAt]; simpa only [sepConj_assoc, arm64_norm] using sepConj_mono_left hrestore)
      exact hcont _ (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hrun])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hsp])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx20])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx23])
        (by simp (config := { failIfUnchanged := false }) only [arm64_norm])
        ⟨by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx26], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx27], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hx28], by simp (config := { failIfUnchanged := false }) only [arm64_norm, hvregs]⟩

theorem chunkedKeysUnsampled_tag1_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest)
    (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.KeysUnsampled) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_305).base + 188#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc' } x.bs rest')
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_305).base + 256#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  refine chunkedKeysUnsampled_uc_init_placed ?_ hpc hrun hsp hx20 hx23 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx24] at hx24_1
  obtain ⟨hx26_1, hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let uc0 : V1State.Unchunked.KeysUnsampled := m.uc.getD default
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hpush_exit := @chunkedKeysUnsampled_uc_push_exit_placed _ A H hPushCall x R s0 { uc := some uc0 }
  have hfrom_push := @chunkedKeysUnsampled_uc_from_push_exit_placed _ A H hFromCall hPushCall x R s0 { uc := some uc0 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_uc_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 outerLimit innerLimit hsp_align hbs_lt hlim_lt
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
    conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach
    refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := entry + 292#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1])
      (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp1, hx19_1]; rfl)
      hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint rest with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        apply hnone_of_uc
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := entry + 616#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0
      have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0)
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := entry + 604#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Unchunked.KeysUnsampled.mergeField (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
            (mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
              (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := entry + 344#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked2CapAt_mono A x.msgPtr uc0.epoch uc0.auth hrest0_le_rest) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc0 x.bs rest0)
          (by dsimp only [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter]; sep_entail)
        exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f => by
            have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
            refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hcs_f
            rw [hres0, hml, hr'_eq]; rfl)
          (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
          (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := entry + 604#64)
    conv => arg 4; rw [chunkedKeysUnsampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (unchunked2CapAt_entails_chunkedKeysUnsampledPBAt A x.msgPtr rest.length uc0) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0 } x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, htr1])
      ⟨by simp only [arm64_norm, hx26_1], by simp only [arm64_norm, hx27_1], by simp only [arm64_norm, hx28_1], by simp only [arm64_norm, hvregs_1]⟩

theorem chunkedKeysUnsampled_loop_le_exit_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63)
    (hnone_of_lt : cur.length < outerLimit →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_305).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (_hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedKeysUnsampledMergeSpec
    simp only [hsome, chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, polySavedRegsAny, polySavedRegs,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, htr, hsp]
    apply SepWP.exists_elim; intro v_pad
    wp_steps
    apply SepWP.fold (stackAt_chunkedInl9_epilogue s0.sp s0 v_pad) (by unfold polySavedRegs; sep_focus)
    wp_done
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt
    have hnone := hnone_of_lt hlt_lim
    have hfrom_err := @chunkedKeysUnsampled_from_err_exit_placed _ A H hFromCall x R s0 m
    apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedKeysUnsampled_decode_key_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur)
    (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State),
      decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_305).base + 248#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_305).base + 188#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt
  let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit_placed _ A H x R s0 m
  have hfrom_err := @chunkedKeysUnsampled_from_err_exit_placed _ A H hFromCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedKeysUnsampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := entry + 208#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
    (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
    wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩
    have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd
    have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le
    have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge
      apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge hwt)
        obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt
        obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge
        obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_keysUnsampled_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := by omega
          apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
          apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
          apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h
            simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := entry + 248#64)
          (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus)
          wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [chunkedKeysUnsampledLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2])
            (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m])
            (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m])
            ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

theorem chunkedKeysUnsampled_dispatch_step_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.KeysUnsampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (htag_lt : tag < 2 ^ 32)
    (htag1 : tag = 1 → ∀ s' : State,
      s'.pc = (blkPl_305).base + 256#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hother : tag ≠ 1 → ∀ s' : State,
      s'.pc = (blkPl_305).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      (s'.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s'
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_305).base + 248#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 1#64)
    (hcs : PolyCalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
      (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx26, hx27, hx28, hvregs⟩ := hcs
  by_cases h1 : tag = 1
  · subst h1
    apply SepWPpLscro.of_sepWP (mid := entry + 256#64); wp_steps; wp_reach
    exact htag1 rfl _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx8]) (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21])
      (by simp only [arm64_norm, hx22]) (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
  · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false h1 htag_lt (by decide : 1 < 2 ^ 32)
    have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
    have hb1_bne1 : (BitVec.ofNat 32 tag != 1#32) = true := by simp only [bne, hb1_1, Bool.not_false]
    have hb1_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 tag) != 1#32) = true := by simp only [bne, hb1_2, Bool.not_false]
    apply SepWPpLscro.of_sepWP (mid := entry + 168#64); wp_steps; wp_reach
    exact hother h1 _ (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      (by simp only [arm64_norm, hx8]) (by simp only [arm64_norm, hx1, sf_truncate32_ofNat64])
      (by simp only [arm64_norm, hx19]) (by simp only [arm64_norm, hx20]) (by simp only [arm64_norm, hx21]) (by simp only [arm64_norm, hx22])
      (by simp only [arm64_norm, hx23]) (by simp only [arm64_norm, hx24])
      ⟨by simp only [arm64_norm, hx26], by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩

theorem chunkedKeysUnsampled_loop_ok_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedKeysUnsampledMergeGhost} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.KeysUnsampled) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_305).base + 188#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 24#5) = 1#64 →
      PolyCalleeSaved s0 s →
      SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s
        (chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur)
        (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0) := by
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    exact chunkedKeysUnsampled_loop_le_exit_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedKeysUnsampled_loop_le_exit_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl)
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedKeysUnsampled_decode_key_step_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd); have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hloop_ok := mergeLoopBin_of_key_ok (m := m) (depth' := 98) protoPrefixStep_chunked_keysUnsampled_mergeField hle_lim hd hk_ge hwt hitag0
      refine chunkedKeysUnsampled_dispatch_step_placed htag_lt ?_ ?_ hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hcs'
      · intro htag1 s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        rw [htag1, chunkedKeysUnsampled_mergeField_tag1] at hloop_ok
        refine chunkedKeysUnsampled_tag1_step_placed hFromCall hPushCall hVarintCall hSkipCall hAuthCall
          hsp_align hbs_lt hrest_le hrest_lt hrest_suf
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
        refine chunkedKeysUnsampled_skip_step_placed hSkipCall hsp_align hrest_le hrest_lt hrest_suf htag_lt
          (fun hsf => by rw [hres, hloop_ok, hsf]; rfl)
          (fun rest' s'' hsf hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs'' => ?_)
          hpc1 hrun1 hsp1 htr1 hx8_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hcs1
        have hrest'_le_rest : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf
        exact ih m rest' s'' (by omega) (by omega)
          (suffix_trans hrest_le hrest_suf hrest'_le_rest ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf))
          (by rw [hres, hloop_ok, hsf]; rfl)
          hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hcs''

theorem chunked_keys_unsampled_merge_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 261) (decodeErrorFromSpec A))
    (hPushCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 257) (decodeErrorPushSpec A))
    (hVarintCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 291) (decodeVarint2Spec A))
    (hSkipCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 263) (skipField3Spec A))
    (hAuthCall : subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A))) :
    subroutine_ok ((blkPC_305).rebase (blkPl_305).base H) (blkPl_305).base
      (withLsCodeRoLoaded lsmpl (chunkedKeysUnsampledMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp
  unfold withLscroProp chunkedKeysUnsampledMergeSpec
  wpp_init x s0
  have hbs_lt : x.bs.length < 2 ^ 63 := h
  replace hpc : s0.pc = (blkPl_305).base := hpc
  conv => arg 6; ext sf P_f; simp only [chunkedKeysUnsampledMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_305).rebase (blkPl_305).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedKeysUnsampledMergeSpec A) x R s0) (WppPanic R s0)
  have hret_err := @chunkedKeysUnsampled_ret_err_exit_placed _ A H x R s0 x.msg
  have hfrom_err := @chunkedKeysUnsampled_from_err_exit_placed _ A H hFromCall x R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedKeysUnsampled_loop_ok_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hAuthCall x R s0 outerLimit hsp_align hbs_lt hlim_lt
  by_cases hwt_ld : x.wt = .lengthDelimited
  · have h_1' : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = 2#8 := by rw [h_1, hwt_ld]; rfl
    have hbeq := wt_beq_two_of_lengthDelimited h_1'
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = false := by
      simp only [bne, hbeq, Bool.not_true]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = false := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1']; decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = false := by
      revert h_1'; bv_bits
    apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, chunkedInlBelow_decodeVarint2 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    wp_reach
    refine SepWPpLscro.call_frame (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := entry + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm])
      (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl)
      hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx26_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := entry + 128#64)
      (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm])
      apply SepWP.pure_elim; rintro ⟨hsm0, htrm, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
      exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm])
        ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩
      have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len
        have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
          rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              conv_rhs => rw [hrest0_suf, List.drop_drop]
              congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.KeysUnsampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := entry + 188#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨⟨hsm0, hsm1⟩, htrm⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedKeysUnsampledPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus)
        wp_steps
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedKeysUnsampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [chunkedKeysUnsampledLoopPre, sliceCursorAfter]; sep_entail)
        exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf hres0
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub])
          (by simp only [arm64_norm]) (by simp only [arm64_norm])
          ⟨by simp only [arm64_norm, hx26_m], by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]
      revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.KeysUnsampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_keysUnsampled_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := entry + 120#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8
    apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0
    wp_steps
    apply SepWP.fold (polySavedRegs_entails_any s0.sp s0 v3) (by unfold polySavedRegs; sep_focus)
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus)
    apply SepWP.fold (chunkedKeysUnsampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedKeysUnsampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [chunkedKeysUnsampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩

alias chunkedKeysUnsampled_merge_placed_ok_of_contracts := chunked_keys_unsampled_merge_placed_ok_of_contracts

end Placed

end CryptoVerification.SpqrV1.Prost.MessageMerge
