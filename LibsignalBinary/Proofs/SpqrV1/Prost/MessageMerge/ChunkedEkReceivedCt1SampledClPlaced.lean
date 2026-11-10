/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1SampledUcClPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase1
import ProofLib.SepLogic.WPp
import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire -- shake: keep

/-!
# Code-Loaded Placed Verification of `Chunked.EkReceivedCt1Sampled::merge` (Block `310`)

Proves the outer loop and top-level contract
`chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts` for
`Chunked.EkReceivedCt1Sampled::merge` on Block `310` with `withLsCodeRoLoaded lsmpl` callee contracts.
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
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen hiding vecU8Buf vecU8At_eq_header_sep_buf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.LibsignalSpqrV1 hiding decodeVarint encodeVarint WireType
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Prost.MessageMerge.Part2

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
attribute [local simp, local arm64_norm] bv64_sub_zero bv64_add_zero chunkedEkReceivedCt1SampledMerge_fnOff

private theorem iwt64_beq_two_of_ne_ld {iwt : WireType} (hne : iwt ≠ .lengthDelimited) :
    (BitVec.ofNat 64 iwt.toNat == 2#64) = false ∧ (BitVec.ofNat 64 iwt.toNat != 2#64) = true := by
  cases iwt <;> simp_all [WireType.toNat]
private theorem setWidth8_zext64_trunc32_ofNat64_wt (wt : WireType) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 wt.toNat))) = BitVec.ofNat 8 wt.toNat := by
  cases wt <;> decide

theorem chunkedEkReceivedCt1Sampled_uc_decode_key_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A))) (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {uc : V1State.Unchunked.Ct1SentEkReceived} {sendingCt1 : Option PolynomialEncoder}
    {cur : List (BitVec 8)} {outerLimit innerLimit : Nat} (hgt_lim : ¬ cur.length ≤ innerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_loop_none :
      mergeLoopBin V1State.Unchunked.Ct1SentEkReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State), decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_310).base + 456#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 0#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 → s'.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit → ChunkedInl10CalleeSaved s0 s' →
      SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 404#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64)
    (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64) (hx26 : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit) (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs cur)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hpush_exit := @chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }
  have hfrom_push := @chunkedEkReceivedCt1Sampled_uc_from_push_exit_cl_placed _ A H hFromCall hPushCall x R s0 { uc := some uc, sendingCt1 := sendingCt1 }
  
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨x.bufRef, x.slot, curPtr, cur⟩) (ret_pc := (blkPl_310).base + 424#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl) hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_unchunked_ct1SentEkReceived_mergeField hgt_lim hd)
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 808#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr cur.length uc sendingCt1) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_unchunked_ct1SentEkReceived_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge; apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr cur.length uc sendingCt1) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
        (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
      exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_unchunked_ct1SentEkReceived_mergeField hgt_lim hd hk_ge hwt); obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr cur.length uc sendingCt1) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
          (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_unchunked_ct1SentEkReceived_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := (by omega); apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr cur.length uc sendingCt1) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc, sendingCt1 := sendingCt1 } x.bs)
            (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
          exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 456#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (unchunked5CapAt_mono A x.msgPtr uc.epoch uc.auth uc.es uc.ek uc.ct1 hrest_le_cur) (by sep_focus); wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs rest)
            (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hx26_m])
            ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Inner loop induction for `Unchunked.Ct1SentEkReceived` at `+0x194` (`(blkPl_310).base + 404#64`). -/
theorem chunkedEkReceivedCt1Sampled_uc_loop_ok_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A))) (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A))) (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) (hAuthCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State}
    {sendingCt1 : Option PolynomialEncoder} {outerLimit innerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : innerLimit < 2 ^ 63) :
    ∀ (n : Nat) (uc : V1State.Unchunked.Ct1SentEkReceived) (cur : List (BitVec 8)) (s : State),
      cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      (∀ (uc' : V1State.Unchunked.Ct1SentEkReceived) (rest' : List (BitVec 8)) (s' : State),
        rest'.length = innerLimit → rest'.length ≤ x.bs.length → IsDropSuffix x.bs rest' →
        mergeLoopBin V1State.Unchunked.Ct1SentEkReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = some uc' →
        s'.pc = (blkPl_310).base + 168#64 →
        s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
        s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
        s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
        ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
          (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc', sendingCt1 := sendingCt1 } x.bs rest')
          (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0)) →
      (mergeLoopBin V1State.Unchunked.Ct1SentEkReceived.mergeField (cur.length - innerLimit) uc cur innerLimit 97 = none →
        (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) →
      s.pc = (blkPl_310).base + 404#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace →
      s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 →
      s.readReg64 (Reg.gpr 25#5) = 8#64 → s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 innerLimit →
      ChunkedInl10CalleeSaved s0 s → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
        (chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc sendingCt1 x.bs cur)
        (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_varint := fun {s uc rest} =>
    @chunkedEkReceivedCt1Sampled_uc_tag1_varint_step_cl_placed _ A H hPushCall hVarintCall x R s0 s uc sendingCt1 rest outerLimit innerLimit
  have htag1_wt_err := fun {s uc rest} =>
    @chunkedEkReceivedCt1Sampled_uc_tag1_wt_err_step_cl_placed _ A H hFromCall hPushCall x R s0 s uc sendingCt1 rest
  have htag2_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_uc_tag2_step_cl_placed _ A H hPushCall hAuthCall x R s0 s uc sendingCt1 rest iwt outerLimit innerLimit
  have htag3_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_uc_tag3_step_cl_placed _ A H hPushCall hBytesCall x R s0 s uc sendingCt1 rest iwt outerLimit innerLimit
  have htag4_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_uc_tag4_step_cl_placed _ A H hPushCall hBytesCall x R s0 s uc sendingCt1 rest iwt outerLimit innerLimit
  have htag5_step := fun {s uc rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_uc_tag5_step_cl_placed _ A H hPushCall hBytesCall x R s0 s uc sendingCt1 rest iwt outerLimit innerLimit
  have hskip_step := fun {s uc rest} (iwt : WireType) (tag : Nat) =>
    @chunkedEkReceivedCt1Sampled_uc_skip_step_cl_placed _ A H hPushCall hSkipCall x R s0 s uc sendingCt1 rest iwt tag outerLimit innerLimit
  intro n; induction n with
  | zero =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    exact chunkedEkReceivedCt1Sampled_uc_loop_le_exit_cl_placed hFromCall hPushCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt)) (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
      hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
  | succ n ih =>
    intro uc cur s hcur_n hcur_le hcur_suf hcont_ok hnone_loop hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    by_cases hle_lim : cur.length ≤ innerLimit
    · exact chunkedEkReceivedCt1Sampled_uc_loop_le_exit_cl_placed hFromCall hPushCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => hnone_loop (mergeLoopBin_lt_limit _ _ _ _ _ _ hlt)) (fun s' heq => hcont_ok uc cur s' heq hcur_le hcur_suf (mergeLoopBin_eq_limit _ _ _ _ _ _ heq))
        hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedEkReceivedCt1Sampled_uc_decode_key_step_cl_placed hFromCall hPushCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf hnone_loop ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx0' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd); have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := uc) (depth' := 97) protoPrefixStep_unchunked_ct1SentEkReceived_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [unchunkedCt1SentEkReceived_mergeField_tag1] at hstep
        
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 608#64); wp_steps; wp_reach
        by_cases hiwt : iwt = .varint
        · subst hiwt
          refine htag1_varint hsp_align hrest_le hrest_lt hrest_suf (fun hdv_none => hnone_loop (by rw [hstep]; simp [hdv_none]))
            (fun v rest' s'' hdv_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_lt : rest'.length < rest.length := decodeVarint_length hdv_some; have hr'_le : rest'.length ≤ rest.length := Nat.le_of_lt hr'_lt
          exact ih { uc with epoch := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (decodeVarint_suffix hdv_some)) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep]; simpa [hdv_some] using hml))
            (fun hml => hnone_loop (by rw [hstep]; simpa [hdv_some] using hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · exact htag1_wt_err hiwt hsp_align hrest_le hrest_suf (hnone_loop (by rw [hstep]; simp [hiwt]))
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [unchunkedCt1SentEkReceived_mergeField_tag2] at hstep
          
          apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 524#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hauth_none => hnone_loop (by rw [hstep, hauth_none]; rfl))
            (fun auth' rest' s'' hauth_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
            ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hauth_some).1
          exact ih { uc with auth := some auth' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hauth_some).2) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hauth_some]; exact hml))
            (fun hml => hnone_loop (by rw [hstep, hauth_some]; exact hml))
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
        · by_cases htag3 : key.toNat / 8 = 3
          · rw [htag3] at hx1' hstep; rw [unchunkedCt1SentEkReceived_mergeField_tag3] at hstep
            
            apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 568#64); wp_steps; wp_reach
            refine htag3_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hmb_none => hnone_loop (by rw [hstep, hmb_none]; rfl))
              (fun v rest' s'' hmb_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
              (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
              ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
            have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb_some
            exact ih { uc with es := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
              (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb_some)) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hmb_some]; exact hml))
              (fun hml => hnone_loop (by rw [hstep, hmb_some]; exact hml))
              hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
          · by_cases htag4 : key.toNat / 8 = 4
            · rw [htag4] at hx1' hstep; rw [unchunkedCt1SentEkReceived_mergeField_tag4] at hstep
              
              apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 588#64); wp_steps; wp_reach
              refine htag4_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hmb_none => hnone_loop (by rw [hstep, hmb_none]; rfl))
                (fun v rest' s'' hmb_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
                ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
              have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb_some
              exact ih { uc with ek := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
                (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb_some)) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hmb_some]; exact hml))
                (fun hml => hnone_loop (by rw [hstep, hmb_some]; exact hml))
                hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
            · by_cases htag5 : key.toNat / 8 = 5
              · rw [htag5] at hx1' hstep; rw [unchunkedCt1SentEkReceived_mergeField_tag5] at hstep
                
                apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 488#64); wp_steps; wp_reach
                refine htag5_step iwt hsp_align hrest_le hrest_lt hrest_suf (fun hmb_none => hnone_loop (by rw [hstep, hmb_none]; rfl))
                  (fun v rest' s'' hmb_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
                  (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
                  ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
                have hr'_le : rest'.length ≤ rest.length := mergeBytes_length hmb_some
                exact ih { uc with ct1 := v } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
                  (suffix_trans hrest_le hrest_suf hr'_le (mergeBytes_suffix hmb_some)) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hmb_some]; exact hml))
                  (fun hml => hnone_loop (by rw [hstep, hmb_some]; exact hml))
                  hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
              · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32); obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
                obtain ⟨hb3_1, _⟩ := itag_beq_tag_false htag3 htag_lt (by decide : 3 < 2 ^ 32); obtain ⟨hb4_1, _⟩ := itag_beq_tag_false htag4 htag_lt (by decide : 4 < 2 ^ 32)
                obtain ⟨hb5_1, _⟩ := itag_beq_tag_false htag5 htag_lt (by decide : 5 < 2 ^ 32)
                have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
                have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
                have hb3_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 3#32) = false := by rw [sf_truncate32_ofNat64]; exact hb3_1
                have hb4_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 4#32) = false := by rw [sf_truncate32_ofNat64]; exact hb4_1
                have hb5_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 5#32) = false := by rw [sf_truncate32_ofNat64]; exact hb5_1
                have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
                have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
                have hb4_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 4#32) = true := by simp only [bne, hb4_1, Bool.not_false]
                have hb4_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 4#32) = true := by simp only [bne, hb4_2, Bool.not_false]
                have hb5_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 5#32) = true := by simp only [bne, hb5_1, Bool.not_false]
                have hb5_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 5#32) = true := by simp only [bne, hb5_2, Bool.not_false]
                rw [unchunkedCt1SentEkReceived_mergeField_other uc iwt rest 97 htag_lt htag1 htag2 htag3 htag4 htag5] at hstep
                
                apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 644#64); wp_steps; wp_reach
                refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt
                  (fun hsf_none => hnone_loop (by rw [hstep, hsf_none]; rfl)) (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs'' => ?_)
                  (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx0']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
                  (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) (by simp only [arm64_norm, hx26'])
                  ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
                have hr'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf_some
                exact ih uc rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
                  (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some)) (fun uc' r' sf hr_eq hr_le hr_suf hml => hcont_ok uc' r' sf hr_eq hr_le hr_suf (by rw [hstep, hsf_some]; exact hml))
                  (fun hml => hnone_loop (by rw [hstep, hsf_some]; exact hml))
                  hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hx26'' hcs''
/-! ## Outer Loop Field Steps (`skip_field`, `tag2 = sendingCt1`, `tag1 = uc`) -/
/-- Outer loop `skip_field` step at `+0x170` (`(blkPl_310).base + 368#64`) for unknown tags (`tag ≠ 1, 2`, `depth' = 98`). -/
theorem chunkedEkReceivedCt1Sampled_skip_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {tag outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (htag_lt : tag < 2 ^ 32)
    (hnone_of_skip : skipField (2 * rest.length + 2) 98 tag iwt rest = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (rest' : List (BitVec 8)) (s' : State),
      skipField (2 * rest.length + 2) 98 tag iwt rest = some rest' →
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest') (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 368#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat) (hx1 : (s.readReg64 (Reg.gpr 1#5)).setWidth 32 = BitVec.ofNat 32 tag) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  have hret := @chunkedEkReceivedCt1Sampled_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 263)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_skipField98 s0.sp]
  simp only [sepConj_assoc]; wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, tag, 98, x.bufRef, x.slot, restPtr, rest⟩) (ret_pc := (blkPl_310).base + 384#64) hSkipCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [skipField3Spec]; simp only [arm64_norm, hsp, hx8, hx1, hx19, setWidth8_zext64_trunc32_ofNat64_wt]; rfl)
    (⟨htag_lt, by decide, hrest_lt⟩ : tag < 2 ^ 32 ∧ 98 < 2 ^ 32 ∧ rest.length < 2 ^ 63) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [skipField3Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hsf : skipField (2 * rest.length + 2) 98 tag iwt rest with
  | none =>
    have hnone := hnone_of_skip hsf
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 128#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    have hcbz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr rest.length m) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hret hnone (by decide : 0 ≤ 3) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some rest' =>
    have hrest'_le : rest'.length ≤ rest.length := (skip_length _).1 _ _ _ _ _ hsf
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 168#64)
    (conv => arg 4; simp only [skipField3Spec, hsf, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩
    apply SepWP.fold (chunkedInlBelow_skipField98_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_mono A x.msgPtr m hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledLoopPre]; sep_entail)
    exact hcont rest' _ hsf (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Shared outer error exit at `+0x348` (`(blkPl_310).base + 840#64`): calls `DecodeError::push` on `(s0.sp - 128#64, err, n)` (`n ≤ 2`), loads `x0` from `[sp]`, and jumps to `ret_err_exit` (`+0x080`). -/
theorem chunkedEkReceivedCt1Sampled_push_ret_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {m : V1State.Chunked.EkReceivedCt1Sampled} {s : State} {err : BitVec 64} {n : Nat}
    (hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none) (hn : n ≤ 2) (herr : err ≠ 0#64) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_310).base + 840#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx0 : s.readReg64 (Reg.gpr 0#5) = s0.sp - 128#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) : SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (((s0.sp - 128#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ memRegion (s0.sp - 120#64) 40 ∗
        stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; have hret := @chunkedEkReceivedCt1Sampled_ret_err_exit_placed _ A H x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 257)
  conv => arg 4; rw [chunkedInlBelow_decodeErrorHook s0.sp, chunkedEkReceivedCt1SampledErrFrame]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := (s0.sp - 128#64, err, n)) (ret_pc := (blkPl_310).base + 844#64) hPushCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [decodeErrorPushSpec]; simp only [arm64_norm, hsp, hx0]; rfl) (by omega : n < 2 ^ 32) (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeErrorPushSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨_, _, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx27, hx28, hvregs] at hpcm hspm hx27_m hx28_m hvregs_m
  apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 128#64)
  (conv => arg 4; simp only [decodeErrorPushSpec, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; intro htrm
  apply SepWP.fold (chunkedInlBelow_decodeErrorHook_entails s0.sp) (by sep_focus); wp_steps
  apply SepWP.fold (pointsTo64_memRegion40_entails_48_160 s0.sp err) (by sep_focus); wp_reach
  apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A err (n + 1) ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
    (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
  exact hret hnone (by omega : n + 1 ≤ 3) herr hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
    (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Outer loop tag 2 (`sendingCt1 : Option<PolynomialEncoder>` at `x.msgPtr + 128#64`) step at `+0x0f4` (`(blkPl_310).base + 244#64`). -/
theorem chunkedEkReceivedCt1Sampled_tag2_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A))) (hPolyCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hrest_le : rest.length ≤ x.bs.length)
    (hrest_suf : IsDropSuffix x.bs rest) (hbound : OptPolyEncoderBound m.sendingCt1 rest.length) (hnone_of_poly :
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (d' : PolynomialEncoder) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption = some (d', rest') →
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some d' } x.bs rest') (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 244#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
      (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  have hpush_ret := fun {d' : PolynomialEncoder} => @chunkedEkReceivedCt1Sampled_push_ret_exit_cl_placed _ A H hPushCall x R s0 { uc := m.uc, sendingCt1 := some d' }
  refine chunkedEkReceivedCt1Sampled_ct1_init_placed ?_ hpc hrun hsp hx20 hx25 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1; rw [hx24] at hx24_1; obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 297)
  conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, chunkedInlBelow_eq_polyMerge s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨iwt, x.msgPtr + 128#64, m.sendingCt1.getD default, x.bufRef, x.slot, restPtr, rest⟩)
    (ret_pc := (blkPl_310).base + 288#64) hPolyCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [polyEncoderMergeSpec]; simp only [arm64_norm, hsp1, hx8_1, hx20_1, hx19_1, setWidth8_zext64_trunc32_ofNat64_wt]; rfl)
    hbound (by sep_focus) (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => by dsimp only [polyEncoderMergeSpec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hpoly_res : (Proto.mergeMessage PolynomialEncoder.mergeField (codecWireTypeToProto iwt) (m.sendingCt1.getD default) rest 98).toOption with
  | none =>
    have hnone := hnone_of_poly hpoly_res; apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 840#64)
    (conv => arg 4; simp only [polyEncoderMergeSpec, hpoly_res, memRegion_48_cells1_160 s0.sp,
      ← chunkedInlBelow_eq_polyMerge s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.exists_elim; intro v_stk0; apply SepWP.exists_elim; intro d'; apply SepWP.exists_elim; intro n_err; apply SepWP.pure_elim; intro hpure
    have htrm : sm.trace = _ := hpure.1; have hsm0 : sm.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hpure.2.1; have hn_err : n_err ≤ 1 := hpure.2.2
    have hcbnz : (sm.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm0; apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
    apply SepWP.fold (optCt1SentEkReceivedPBCapAt_entails A x.msgPtr rest.length m.uc) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ sm.readReg64 (Reg.gpr 0#5)) ∗ decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 0#5)) n_err ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := m.uc, sendingCt1 := some d' } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame, chunkedEkReceivedCt1SampledPBAt]; rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
    exact hpush_ret hnone (by omega : n_err ≤ 2) hsm0 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hspm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨d', rest'⟩; have hrest'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_res).1; apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 168#64)
    (conv => arg 4; simp only [polyEncoderMergeSpec, hpoly_res, ← chunkedInlBelow_eq_polyMerge s0.sp,
      sepConj_assoc, arm64_norm, hsp1])
    apply SepWP.pure_elim; rintro ⟨htrm, hsm0⟩; apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest'_le) (by sep_focus)
    apply SepWP.fold (optCt1SentEkReceivedPBCapAt_mono A x.msgPtr m.uc hrest'_le) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with sendingCt1 := some d' } x.bs rest')
      (by dsimp only [chunkedEkReceivedCt1SampledLoopPre, chunkedEkReceivedCt1SampledPBCapAt]; rw [optPolynomialEncoderPBAt_some_eq]; sep_entail)
    exact hcont d' rest' _ hpoly_res (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1])
      (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩

/-- Outer loop tag 1 (`uc : Option<Unchunked.Ct1SentEkReceived>`) step at `+0x12c` (`(blkPl_310).base + 300#64`). -/
theorem chunkedEkReceivedCt1Sampled_tag1_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A))) (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A))) (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) (hAuthCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled} {rest : List (BitVec 8)} {iwt : WireType} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63)
    (hrest_le : rest.length ≤ x.bs.length) (hrest_lt : rest.length < 2 ^ 63) (hrest_suf : IsDropSuffix x.bs rest) (hnone_of_uc :
      (Proto.mergeMessage V1State.Unchunked.Ct1SentEkReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (uc' : V1State.Unchunked.Ct1SentEkReceived) (rest' : List (BitVec 8)) (s' : State),
      (Proto.mergeMessage V1State.Unchunked.Ct1SentEkReceived.mergeField (codecWireTypeToProto iwt) (m.uc.getD default) rest 98).toOption = some (uc', rest') →
      s'.pc = (blkPl_310).base + 168#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace →
      s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr { m with uc := some uc' } x.bs rest') (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 300#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit) (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  let uc0 : V1State.Unchunked.Ct1SentEkReceived := m.uc.getD default; have hpush_exit := @chunkedEkReceivedCt1Sampled_uc_push_exit_cl_placed _ A H hPushCall x R s0 { uc := some uc0, sendingCt1 := m.sendingCt1 }
  have hfrom_push := @chunkedEkReceivedCt1Sampled_uc_from_push_exit_cl_placed _ A H hFromCall hPushCall x R s0 { uc := some uc0, sendingCt1 := m.sendingCt1 }
  have huc_loop := fun (innerLimit : Nat) (hlim_lt : innerLimit < 2 ^ 63) =>
    @chunkedEkReceivedCt1Sampled_uc_loop_ok_cl_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall x R s0 m.sendingCt1 outerLimit innerLimit hsp_align hbs_lt hlim_lt
  refine chunkedEkReceivedCt1Sampled_uc_init_placed ?_ hpc hrun hsp hx20 hx23 hx24 hcs
  intro s1 hpc1 hrun1 hsp1 htr1 hx8_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hcs1
  rw [htr] at htr1; rw [hx8] at hx8_1; rw [hx19] at hx19_1; rw [hx21] at hx21_1; rw [hx22] at hx22_1; rw [hx25] at hx25_1; obtain ⟨hx27_1, hx28_1, hvregs_1⟩ := hcs1
  let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
  
  by_cases hiwt : iwt = .lengthDelimited
  · subst hiwt
    apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf,
      chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
    wp_steps; wp_reach
    refine SepWPpLscro.call_frame_lscro (x := ⟨x.bufRef, x.slot, restPtr, rest⟩)
      (ret_pc := (blkPl_310).base + 352#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [State.spAligned, hsp1, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp1, hx19_1]; rfl) hrest_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr1]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
    simp (config := { decide := true }) only [arm64_norm, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hvregs_1] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint rest with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        apply hnone_of_uc
        rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1SentEkReceived_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 808#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      have hcbnz : (sm.readReg64 (Reg.gpr 1#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hsm1; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc0 m.sendingCt1) (by sep_focus)
      wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0, sendingCt1 := m.sendingCt1 } x.bs)
        (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
      exact hpush_exit hnone (by decide : 0 ≤ 2) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩; have hrest0_lt_rest : rest0.length < rest.length := decodeVarint_length hdv0; have hrest0_le_rest : rest0.length ≤ rest.length := Nat.le_of_lt hrest0_lt_rest
      have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_trans hrest0_le_rest hrest_le; have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt
      have hrest0_suf : IsDropSuffix x.bs rest0 := suffix_trans hrest_le hrest_suf hrest0_le_rest (decodeVarint_suffix hdv0); let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt; have hult : (BitVec.ofNat 64 rest0.length).ult len = true := by simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest0.length < 2 ^ 64), decide_eq_true_eq]; exact hlt_len
        have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          apply hnone_of_uc
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1SentEkReceived_mergeField]; rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, memRegion_48_cells1_160 s0.sp,
          sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm, hsp1])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc0 m.sendingCt1) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps; apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus)
        apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0, sendingCt1 := m.sendingCt1 } x.bs)
          (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
        exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt; have hult : (BitVec.ofNat 64 rest0.length).ult len = false := by simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rest0.length < 2 ^ 64), decide_eq_false_iff_not]; exact hlt_len
        have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Unchunked.Ct1SentEkReceived.mergeField (codecWireTypeToProto .lengthDelimited) uc0 rest 98).toOption =
            (mergeLoopBin V1State.Unchunked.Ct1SentEkReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97).map
              (fun uc' => (uc', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1SentEkReceived_mergeField]; rcases hdv0_p : Proto.decodeVarint rest with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint rest = none := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint rest = some (len', rest0') := by rw [← proto_decodeVarint_toOption rest, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              (conv_rhs => rw [hrest0_suf, List.drop_drop]); congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Unchunked.Ct1SentEkReceived.mergeField (rest0.length - (rest0.length - len.toNat)) uc0 rest0 (rest0.length - len.toNat) 97 with _ | uc' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 404#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm, hsp1]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hrest_le hrest_suf hrest0_le_rest) (by sep_focus)
        apply SepWP.fold (unchunked5CapAt_mono A x.msgPtr uc0.epoch uc0.auth uc0.es uc0.ek uc0.ct1 hrest0_le_rest) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest0_le hrest0_suf, sliceCursorAt]
        simp only [sepConj_assoc]; wp_steps; apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledUcLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr uc0 m.sendingCt1 x.bs rest0)
          (by dsimp only [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter]; sep_entail)
        exact huc_loop (rest0.length - len.toNat) hlim_lt rest0.length uc0 rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (fun uc' r' sf hr_eq hr_le hr_suf hml hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f => by
            have hr'_eq : r' = x.bs.drop (x.bs.length - (rest0.length - len.toNat)) := by rw [hr_suf, hr_eq]
            refine hcont uc' r' sf ?_ hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f hx24_f hx25_f hcs_f
            rw [hres0, hml, hr'_eq]; rfl) (fun hml => hnone_of_uc (by rw [hres0, hml]; rfl))
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr1]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) (by simp only [arm64_norm, hsm1, hsub])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · obtain ⟨hcmp1, hcmp2⟩ := iwt64_beq_two_of_ne_ld hiwt
    have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      apply hnone_of_uc
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_unchunked_ct1SentEkReceived_mergeField]
      unfold mergeMessageBin; revert hiwt; cases iwt <;> intro hiwt <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 796#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledUcLoopPre, sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro b_wt1; apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps
    apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus); apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus)
    apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus); apply SepWP.fold (unchunked5CapAt_entails_chunkedEkReceivedCt1SampledPBAt A x.msgPtr rest.length uc0 m.sendingCt1) (by sep_focus)
    wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr { uc := some uc0, sendingCt1 := m.sendingCt1 } x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hfrom_push hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun1]) (by simp only [arm64_norm, hsp1]) (by simp only [arm64_norm, htr1])
      ⟨by simp only [arm64_norm, hx27_1], by simp only [arm64_norm, hx28_1], by simp only [arm64_norm, hvregs_1]⟩
/-- Outer loop exit at `+0x0a8` (`(blkPl_310).base + 168#64`) when `cur.length ≤ outerLimit`. -/
theorem chunkedEkReceivedCt1Sampled_loop_le_exit_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hle_lim : cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_suf : IsDropSuffix x.bs cur) (hlim_lt : outerLimit < 2 ^ 63) (hnone_of_lt : cur.length < outerLimit →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hsome_of_eq : cur.length = outerLimit →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = some (m, cur))
    (hpc : s.pc = (blkPl_310).base + 168#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (_hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (_hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (_hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (_hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (_hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  by_cases heq_lim : cur.length = outerLimit
  · obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_eq heq_lim
    have hsome := hsome_of_eq heq_lim
    apply SepWPpLscro.of_sepWP_ret; unfold WppPost chunkedEkReceivedCt1SampledMergeSpec
    simp only [hsome, chunkedEkReceivedCt1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
      sliceCursorAt, chunkedInlSavedRegs10, sepConj_assoc, arm64_norm, htr, hsp]
    wp_steps; apply SepWP.fold (stackAt_chunkedInl10_epilogue s0.sp s0) (by unfold chunkedInlSavedRegs10; sep_focus)
    wp_done
  · have hlt_lim : cur.length < outerLimit := Nat.lt_of_le_of_ne hle_lim heq_lim
    obtain ⟨hcmp1, hcmp2, hcmp3⟩ := cmp_len_limit_of_lt hlt_lim hlim_lt; have hnone := hnone_of_lt hlt_lim; have hfrom_err := @chunkedEkReceivedCt1Sampled_from_err_exit_cl_placed _ A H hFromCall x R s0 m
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64)
    conv => arg 4; rw [chunkedEkReceivedCt1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_stk0; wp_steps
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot curPtr (BitVec.ofNat 64 cur.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000008#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000008#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm, hsp]) (by simp only [arm64_norm, htr])
      ⟨by simp only [arm64_norm, hx27], by simp only [arm64_norm, hx28], by simp only [arm64_norm, hvregs]⟩
/-- Outer loop key-decode step at `+0x0a8` (`(blkPl_310).base + 168#64`) when `¬ cur.length ≤ outerLimit`. -/
theorem chunkedEkReceivedCt1Sampled_decode_key_step_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A))) (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 s : State}
    {m : V1State.Chunked.EkReceivedCt1Sampled} {cur : List (BitVec 8)} {outerLimit : Nat}
    (hgt_lim : ¬ cur.length ≤ outerLimit) (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hcur_le : cur.length ≤ x.bs.length) (hcur_lt : cur.length < 2 ^ 63) (hcur_suf : IsDropSuffix x.bs cur) (hnone_of_loop_none :
      mergeLoopBin V1State.Chunked.EkReceivedCt1Sampled.mergeField (cur.length - outerLimit) m cur outerLimit 98 = none →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none)
    (hcont : ∀ (key : BitVec 64) (iwt : WireType) (rest : List (BitVec 8)) (s' : State), decodeVarint cur = some (key, rest) → ¬ 2 ^ 32 ≤ key.toNat →
      WireType.ofNat? (key.toNat % 8) = some iwt → ¬ key.toNat / 8 < 1 →
      s'.pc = (blkPl_310).base + 228#64 →
      s'.status = .Running → s'.sp = s0.sp - 128#64 → s'.trace = s0.trace → s'.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 iwt.toNat →
      s'.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (key.toNat / 8) → s'.readReg64 (Reg.gpr 19#5) = x.bufRef → s'.readReg64 (Reg.gpr 20#5) = x.msgPtr → s'.readReg64 (Reg.gpr 21#5) = x.slot → s'.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s'.readReg64 (Reg.gpr 23#5) = 1#64 → s'.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s'.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s' → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s'
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0))
    (hpc : s.pc = (blkPl_310).base + 168#64) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 128#64) (htr : s.trace = s0.trace) (hx19 : s.readReg64 (Reg.gpr 19#5) = x.bufRef) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.msgPtr) (hx21 : s.readReg64 (Reg.gpr 21#5) = x.slot) (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit)
    (hx23 : s.readReg64 (Reg.gpr 23#5) = 1#64) (hx24 : s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64) (hx25 : s.readReg64 (Reg.gpr 25#5) = 8#64)
    (hcs : ChunkedInl10CalleeSaved s0 s) :
    SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
      (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  obtain ⟨hx27, hx28, hvregs⟩ := hcs; obtain ⟨hcmp1, hcmp2⟩ := cmp_len_limit_of_gt hgt_lim hcur_lt; let curPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - cur.length)
  have hret_err := @chunkedEkReceivedCt1Sampled_ret_err_exit_placed _ A H x R s0 m; have hfrom_err := @chunkedEkReceivedCt1Sampled_from_err_exit_cl_placed _ A H hFromCall x R s0 m
  apply SepWPpLscro.of_sepWP (mid := lsmpl.base 291)
  conv => arg 4; rw [chunkedEkReceivedCt1SampledLoopPre, sliceCursorAfter_eq_split hcur_le hcur_suf,
    sliceCursorAt, chunkedInlBelow_decodeVarint2 s0.sp]; simp only [sepConj_assoc]
  wp_steps; wp_reach
  refine SepWPpLscro.call_frame_lscro (x := ⟨x.bufRef, x.slot, curPtr, cur⟩)
    (ret_pc := (blkPl_310).base + 188#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [State.spAligned, hsp, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, hsp, hx19]; rfl)
    hcur_lt (by dsimp only [sliceCursorAt, curPtr]; sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm, htr]) hpan) ?_
  intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx25_m, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm, hsp, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hx28, hvregs] at hpcm hrunm hspm hx19_m hx20_m hx21_m hx22_m hx23_m hx24_m hx25_m hx27_m hx28_m hvregs_m
  cases hd : decodeVarint cur with
  | none =>
    have hnone := hnone_of_loop_none (mergeLoopBin_of_decodeVarint_none protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField hgt_lim hd); apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 128#64)
    (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
    apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hcur_le hcur_suf) (by sep_focus)
    apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus); wp_steps; wp_reach
    apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
      (by simp only [arm64_norm, htrm, htr]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  | some p =>
    rcases p with ⟨key, rest⟩; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
    have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
    let restPtr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest.length)
    by_cases hk_ge : 2 ^ 32 ≤ key.toNat
    · have hnone := hnone_of_loop_none (mergeLoopBin_of_key_ge protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField hgt_lim hd hk_ge)
      have hshr := key_shr32_of_ge hk_ge; apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
      apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
      apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
      conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
      have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ key) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
        rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp key
      apply SepWP.fold h40 (by sep_focus); wp_reach
      apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000004#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
        (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
      exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000004#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
        ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    · have hshr := key_shr32_of_lt hk_ge
      cases hwt : WireType.ofNat? (key.toNat % 8) with
      | none =>
        have hnone := hnone_of_loop_none (mergeLoopBin_of_wt_none protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField hgt_lim hd hk_ge hwt); obtain ⟨hcs1, hcs2⟩ := key_wt_none hwt
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
        apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
        apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
        conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells2_160 s0.sp]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; apply SepWP.exists_elim; intro v_err1; wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
        have h40 : ((s0.sp - 128#64 + 8#64) ↦₆₄ (key &&& 7#64)) ∗ memRegion (s0.sp - 112#64) 32 ⊢ memRegion (s0.sp - 120#64) 40 := by
          rw [bv_sub_add_lit s0.sp 128 8]; exact cells2_memRegion32_entails_40_160 s0.sp (key &&& 7#64)
        apply SepWP.fold h40 (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000003#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
          (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000003#64) hsp_align
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      | some iwt =>
        obtain ⟨hcc1, hcc2, hand_wt, hcc1_wt, hcc2_wt⟩ := key_wt_some hwt; obtain ⟨hw1, hw1_2⟩ := w1_tag_eq hk_ge; obtain ⟨hw1_zext1, hw1_zext2⟩ := bv32_zeroExtend_ofNat (n := key.toNat / 8) (by omega)
        by_cases hitag0 : key.toNat / 8 < 1
        · have hnone := hnone_of_loop_none (mergeLoopBin_of_tag_zero protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField hgt_lim hd hk_ge hwt hitag0)
          have htag_zero : key.toNat / 8 = 0 := (by omega); apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp])
          apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
          apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus); apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr cur.length m) (by sep_focus)
          conv => arg 4; rw [sliceCursorAfter_eq_split hrest_le hrest_suf, sliceCursorAt, memRegion_48_cells1_160 s0.sp]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v_err0; wp_steps
          apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot restPtr (BitVec.ofNat 64 rest.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest_le hrest_suf) (by sep_focus)
          wp_reach
          apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000005#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs)
            (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
          exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000005#64) hsp_align
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
        · obtain ⟨hcbz_tag1, hcbz_tag2⟩ := tag_cbz_false hk_ge hitag0
          have hcbz_tag64 : (BitVec.ofNat 64 (key.toNat / 8) == 0#64) = false := by
            rw [beq_eq_false_iff_ne]; intro h; have h1 := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : key.toNat / 8 < 2 ^ 64)] at h1; omega
          apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 228#64); (conv => arg 4; simp only [decodeVarint2Spec, hd, sepConj_assoc, arm64_norm, hsp]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
          apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (sliceCursorAfter_join hcur_le hcur_suf hrest_le_cur) (by sep_focus)
          apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_mono A x.msgPtr m hrest_le_cur) (by sep_focus); wp_steps; wp_reach
          apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs rest)
            (by dsimp only [chunkedEkReceivedCt1SampledLoopPre]; sep_entail)
          exact hcont key iwt rest _ hd hk_ge hwt hitag0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm, htr])
            (by simp only [arm64_norm, hsm1, hand_wt]) (by simp only [arm64_norm, hsm1, hw1, hw1_2, hw1_zext1, hw1_zext2]) (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm, hx21_m]) (by simp only [arm64_norm, hx22_m]) (by simp only [arm64_norm, hx23_m]) (by simp only [arm64_norm, hx24_m]) (by simp only [arm64_norm, hx25_m]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
/-- Main outer loop induction at `+0x0a8` (`(blkPl_310).base + 168#64`) for `V1State.Chunked.EkReceivedCt1Sampled.mergeField`. -/
theorem chunkedEkReceivedCt1Sampled_loop_ok_cl_placed [LibsignalPlacement] {A : RustAlloc} {H : String → Option (State → State)}
    (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A))) (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A))) (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A))) (hAuthCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    (hPolyCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A)))
    {x : ChunkedEkReceivedCt1SampledMergeGhost} {R : SepProp} {s0 : State} {outerLimit : Nat}
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) (hbs_lt : x.bs.length < 2 ^ 63) (hlim_lt : outerLimit < 2 ^ 63) :
    ∀ (n : Nat) (m : V1State.Chunked.EkReceivedCt1Sampled) (cur : List (BitVec 8)) (s : State), cur.length ≤ n → cur.length ≤ x.bs.length → IsDropSuffix x.bs cur →
      OptPolyEncoderBound m.sendingCt1 cur.length →
      (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
        (mergeLoopBin V1State.Chunked.EkReceivedCt1Sampled.mergeField (cur.length - outerLimit) m cur outerLimit 98).map
          (fun m' => (m', x.bs.drop (x.bs.length - outerLimit))) →
      s.pc = (blkPl_310).base + 168#64 →
      s.status = .Running → s.sp = s0.sp - 128#64 → s.trace = s0.trace → s.readReg64 (Reg.gpr 19#5) = x.bufRef → s.readReg64 (Reg.gpr 20#5) = x.msgPtr →
      s.readReg64 (Reg.gpr 21#5) = x.slot → s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 outerLimit →
      s.readReg64 (Reg.gpr 23#5) = 1#64 → s.readReg64 (Reg.gpr 24#5) = 0xffffffffffffffff#64 → s.readReg64 (Reg.gpr 25#5) = 8#64 →
      ChunkedInl10CalleeSaved s0 s → SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s
        (chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr m x.bs cur) (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0) := by
  have htag1_step := fun {s m rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_tag1_step_cl_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall x R s0 s m rest iwt outerLimit
  have htag2_step := fun {s m rest} (iwt : WireType) =>
    @chunkedEkReceivedCt1Sampled_tag2_step_cl_placed _ A H hPushCall hPolyCall x R s0 s m rest iwt outerLimit
  have hskip_step := fun {s m rest} (iwt : WireType) (tag : Nat) =>
    @chunkedEkReceivedCt1Sampled_skip_step_cl_placed _ A H hSkipCall x R s0 s m rest iwt tag outerLimit
  intro n; induction n with
  | zero =>
    intro m cur s hcur_n hcur_le hcur_suf _ hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    exact chunkedEkReceivedCt1Sampled_loop_le_exit_cl_placed hFromCall (by omega) hsp_align hcur_le hcur_suf hlim_lt
      (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
      (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl) hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
  | succ n ih =>
    intro m cur s hcur_n hcur_le hcur_suf hbound hres hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    by_cases hle_lim : cur.length ≤ outerLimit
    · exact chunkedEkReceivedCt1Sampled_loop_le_exit_cl_placed hFromCall hle_lim hsp_align hcur_le hcur_suf hlim_lt
        (fun hlt => by rw [hres, mergeLoopBin_lt_limit _ _ _ _ _ _ hlt]; rfl)
        (fun heq => by rw [hres, mergeLoopBin_eq_limit _ _ _ _ _ _ heq, ← heq, ← hcur_suf]; rfl) hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
    · have hcur_lt : cur.length < 2 ^ 63 := Nat.lt_of_le_of_lt hcur_le hbs_lt
      refine chunkedEkReceivedCt1Sampled_decode_key_step_cl_placed hFromCall hVarintCall hle_lim hsp_align
        hcur_le hcur_lt hcur_suf (fun hml => by rw [hres, hml]; rfl) ?_ hpc hrun hsp htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hcs
      intro key iwt rest s' hd hk_ge hwt hitag0 hpc' hrun' hsp' htr' hx8' hx1' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hcs'
      obtain ⟨hx27', hx28', hvregs'⟩ := hcs'; have hrest_lt_cur : rest.length < cur.length := decodeVarint_length hd; have hrest_le_cur : rest.length ≤ cur.length := Nat.le_of_lt hrest_lt_cur
      have hrest_le : rest.length ≤ x.bs.length := Nat.le_trans hrest_le_cur hcur_le; have hrest_lt : rest.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest_le hbs_lt
      have hrest_suf : IsDropSuffix x.bs rest := suffix_trans hcur_le hcur_suf hrest_le_cur (decodeVarint_suffix hd)
      have hbound_rest : OptPolyEncoderBound m.sendingCt1 rest.length := optPolyEncoderBound_mono hbound hrest_le_cur; have htag_lt : key.toNat / 8 < 2 ^ 32 := by omega
      have hstep := mergeLoopBin_of_key_ok (m := m) (depth' := 98) protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField hle_lim hd hk_ge hwt hitag0
      by_cases htag1 : key.toNat / 8 = 1
      · rw [htag1] at hx1' hstep; rw [chunkedEkReceivedCt1Sampled_mergeField_tag1] at hstep
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 300#64); wp_steps; wp_reach
        refine htag1_step iwt hsp_align hbs_lt hrest_le hrest_lt hrest_suf (fun huc_none => by rw [hres, hstep, huc_none]; rfl)
          (fun uc' rest' s'' huc_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
          (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
        have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix huc_some).1
        exact ih { m with uc := some uc' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
          (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix huc_some).2) (optPolyEncoderBound_mono hbound_rest hr'_le)
          (by rw [hres, hstep, huc_some]; rfl) hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
      · by_cases htag2 : key.toNat / 8 = 2
        · rw [htag2] at hx1' hstep; rw [chunkedEkReceivedCt1Sampled_mergeField_tag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 244#64); wp_steps; wp_reach
          refine htag2_step iwt hsp_align hrest_le hrest_suf hbound_rest (fun hpoly_none => by rw [hres, hstep, hpoly_none]; rfl)
            (fun d' rest' s'' hpoly_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20']) (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23'])
            (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (proto_mergeMessage_suffix hpoly_some).1
          exact ih { m with sendingCt1 := some d' } rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le (proto_mergeMessage_suffix hpoly_some).2) (optPolyEncoderBound_of_merge hbound_rest hpoly_some)
            (by rw [hres, hstep, hpoly_some]; rfl) hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''
        · obtain ⟨hb1_1, _⟩ := itag_beq_tag_false htag1 htag_lt (by decide : 1 < 2 ^ 32)
          obtain ⟨hb2_1, _⟩ := itag_beq_tag_false htag2 htag_lt (by decide : 2 < 2 ^ 32)
          have hb1_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 1#32) = false := by rw [sf_truncate32_ofNat64]; exact hb1_1
          have hb2_2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) == 2#32) = false := by rw [sf_truncate32_ofNat64]; exact hb2_1
          have hb2_bne1 : (BitVec.ofNat 32 (key.toNat / 8) != 2#32) = true := by simp only [bne, hb2_1, Bool.not_false]
          have hb2_bne2 : (BitVec.truncate 32 (BitVec.ofNat 64 (key.toNat / 8)) != 2#32) = true := by simp only [bne, hb2_2, Bool.not_false]
          rw [chunkedEkReceivedCt1Sampled_mergeField_other m iwt rest 98 htag_lt htag1 htag2] at hstep
          apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 368#64); wp_steps; wp_reach
          refine hskip_step iwt (key.toNat / 8) hsp_align hrest_le hrest_lt hrest_suf htag_lt (fun hsf_none => by rw [hres, hstep, hsf_none]; rfl)
            (fun rest' s'' hsf_some hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs'' => ?_) (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun']) (by simp only [arm64_norm, hsp']) (by simp only [arm64_norm, htr']) (by simp only [arm64_norm, hx8']) (by simp only [arm64_norm, hx1', sf_truncate32_ofNat64]) (by simp only [arm64_norm, hx19']) (by simp only [arm64_norm, hx20'])
            (by simp only [arm64_norm, hx21']) (by simp only [arm64_norm, hx22']) (by simp only [arm64_norm, hx23']) (by simp only [arm64_norm, hx24']) (by simp only [arm64_norm, hx25']) ⟨by simp only [arm64_norm, hx27'], by simp only [arm64_norm, hx28'], by simp only [arm64_norm, hvregs']⟩
          have hr'_le : rest'.length ≤ rest.length := (skip_length (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some
          exact ih m rest' s'' (by omega) (Nat.le_trans hr'_le hrest_le)
            (suffix_trans hrest_le hrest_suf hr'_le ((skip_suffix (2 * rest.length + 2)).1 _ _ _ _ _ hsf_some)) (optPolyEncoderBound_mono hbound_rest hr'_le) (by rw [hres, hstep, hsf_some]; rfl)
            hpc'' hrun'' hsp'' htr'' hx19'' hx20'' hx21'' hx22'' hx23'' hx24'' hx25'' hcs''

theorem chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hFromCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 261) (withLsCodeRoLoaded lsmpl (decodeErrorFromSpec A)))
    (hPushCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 257) (withLsCodeRoLoaded lsmpl (decodeErrorPushSpec A)))
    (hVarintCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 291) (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A)))
    (hSkipCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 263) (withLsCodeRoLoaded lsmpl (skipField3Spec A)))
    (hBytesCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A)))
    (hAuthCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 295) (withLsCodeRoLoaded lsmpl (authMergeSpec A)))
    (hPolyCall : subroutine_ok ((blkPC_310).rebase (blkPl_310).base H)
      (lsmpl.base 297) (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A))) :
    subroutine_ok ((blkPC_310).rebase (blkPl_310).base H) ((blkPl_310).base)
      (withLsCodeRoLoaded lsmpl (chunkedEkReceivedCt1SampledMergeSpec A)) := by
  apply subroutine_ok_withLsCodeRoLoaded_of_withLscroProp; unfold withLscroProp chunkedEkReceivedCt1SampledMergeSpec; wpp_init x s0
  have hbound : OptPolyEncoderBound x.msg.sendingCt1 x.bs.length := h
  have hbs_lt : x.bs.length < 2 ^ 63 := by unfold OptPolyEncoderBound at hbound; omega
  replace hpc : s0.pc = (blkPl_310).base := hpc
  conv => arg 6; ext sf P_f; simp only [chunkedEkReceivedCt1SampledMergeSpec, sepConj_assoc, satisfies_pure_sepConj]
  apply SepWPp.elim_lscroProp
  change SepWPpLscro lsmpl ((blkPC_310).rebase (blkPl_310).base H) (s0.readReg64 Reg.lr) s0
    _ (WppPost (chunkedEkReceivedCt1SampledMergeSpec A) x R s0) (WppPanic R s0)
  have hret_err := @chunkedEkReceivedCt1Sampled_ret_err_exit_placed _ A H x R s0 x.msg; have hfrom_err := @chunkedEkReceivedCt1Sampled_from_err_exit_cl_placed _ A H hFromCall x R s0 x.msg
  have hloop := fun (outerLimit : Nat) (hlim_lt : outerLimit < 2 ^ 63) =>
    @chunkedEkReceivedCt1Sampled_loop_ok_cl_placed _ A H hFromCall hPushCall hVarintCall hSkipCall hBytesCall hAuthCall hPolyCall x R s0 outerLimit hsp_align hbs_lt hlim_lt
  have hsaved : ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      chunkedInlSavedRegs10 s0.sp s0 := Entails.refl _
  
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
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5
    apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9; wp_steps; apply SepWP.fold hsaved (by sep_focus); wp_reach
    refine SepWPpLscro.call_frame_lscro (spec := decodeVarint2Spec A) (x := ⟨x.bufRef, x.slot, x.ptr, x.bs⟩)
      (ret_pc := (blkPl_310).base + 56#64) hVarintCall (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [State.spAligned, arm64_norm]; exact hsp_align) (by simp only [arm64_norm]) (by dsimp only [decodeVarint2Spec]; simp only [arm64_norm, h_3]; rfl) hbs_lt (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex) (fun sf _ hpan => by dsimp only [decodeVarint2Spec] at hpan; exact allowPanic_frame' (by simp only [arm64_norm]) hpan) ?_
    intro sm hpcm hrunm hspm hcsm; simp only [CalleeSavedPreserved] at hcsm
    obtain ⟨hx19_m, hx20_m, _, _, _, _, _, _, hx27_m, hx28_m, _, hvregs_m⟩ := hcsm; simp (config := { decide := true }) only [arm64_norm, h_2, h_3] at hpcm hrunm hspm hx19_m hx20_m hx27_m hx28_m hvregs_m
    cases hdv0 : decodeVarint x.bs with
    | none =>
      have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
        rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField]
        simp [mergeMessageBin, codecWireTypeToProto, proto_decodeVarint_toOption, hdv0]
      apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 128#64); (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sepConj_assoc, arm64_norm]); apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩
      apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus); apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_steps; wp_reach
      apply SepWPpLscro.weaken_pre (P' := decodeErrorAtStackLen A (sm.readReg64 (Reg.gpr 1#5)) 0 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ memRegion (s0.sp - 128#64) 48 ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
        (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
      exact hret_err hnone (by decide : 0 ≤ 3) hsm1 hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm])
        (by simp only [arm64_norm, htrm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
    | some p =>
      rcases p with ⟨len, rest0⟩; have hrest0_lt_bs : rest0.length < x.bs.length := decodeVarint_length hdv0; have hrest0_le : rest0.length ≤ x.bs.length := Nat.le_of_lt hrest0_lt_bs
      have hrest0_lt : rest0.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrest0_le hbs_lt; have hrest0_suf : IsDropSuffix x.bs rest0 := decodeVarint_suffix hdv0
      let rest0Ptr : BitVec 64 := x.ptr + BitVec.ofNat 64 (x.bs.length - rest0.length)
      by_cases hlt_len : rest0.length < len.toNat
      · have hule := ule_len_of_lt hlt_len hrest0_lt
        have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField]; rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            simp [mergeMessageBin, codecWireTypeToProto, hdv0_p, Except.toOption, hlt_len]
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, memRegion_48_cells1_160 s0.sp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm])
        apply SepWP.exists_elim; intro v_stk0; apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_steps
        apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot rest0Ptr (BitVec.ofNat 64 rest0.length)) (by sep_focus); apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus)
        wp_reach
        apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000007#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
          (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
        exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000007#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
      · have hule := ule_len_of_ge hlt_len hrest0_lt
        have hsub := bv_len_sub_limit hlt_len; have hlim_lt : rest0.length - len.toNat < 2 ^ 63 := by omega
        have hres0 : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption =
            (mergeLoopBin V1State.Chunked.EkReceivedCt1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98).map
              (fun m' => (m', x.bs.drop (x.bs.length - (rest0.length - len.toNat)))) := by
          rw [hwt_ld, ← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField]; rcases hdv0_p : Proto.decodeVarint x.bs with e | ⟨len', rest0'⟩
          · have hdv0' : decodeVarint x.bs = none := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; nomatch hdv0'
          · have hdv0' : decodeVarint x.bs = some (len', rest0') := by rw [← proto_decodeVarint_toOption x.bs, hdv0_p]; rfl
            rw [hdv0] at hdv0'; injection hdv0' with hp; injection hp with hl hr0; subst hl hr0
            have hdrop_eq : x.bs.drop (x.bs.length - (rest0.length - len.toNat)) = rest0.drop len.toNat := by
              (conv_rhs => rw [hrest0_suf, List.drop_drop]); congr 1; omega
            simp only [mergeMessageBin, codecWireTypeToProto, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
              hdv0_p, Except.toOption, hlt_len, hdrop_eq]
            rcases mergeLoopBin V1State.Chunked.EkReceivedCt1Sampled.mergeField (rest0.length - (rest0.length - len.toNat)) x.msg rest0 (rest0.length - len.toNat) 98 with _ | m' <;> rfl
        apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 168#64)
        (conv => arg 4; simp only [decodeVarint2Spec, hdv0, sliceCursorAfter_eq_split hrest0_le hrest0_suf,
          sliceCursorAt, sepConj_assoc, arm64_norm])
        apply SepWP.pure_elim; rintro ⟨htrm, hsm0, hsm1⟩; apply SepWP.fold (chunkedInlBelow_decodeVarint2_entails s0.sp) (by sep_focus)
        apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_mono A x.msgPtr x.msg hrest0_le) (by sep_focus); wp_steps; apply SepWP.fold (pointsToBytes_prefix_join hrest0_le hrest0_suf) (by sep_focus); wp_reach
        apply SepWPpLscro.weaken_pre (P' := chunkedEkReceivedCt1SampledLoopPre A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs rest0)
          (by dsimp only [chunkedEkReceivedCt1SampledLoopPre, sliceCursorAfter]; sep_entail)
        exact hloop (rest0.length - len.toNat) hlim_lt rest0.length x.msg rest0 _ (Nat.le_refl _) hrest0_le hrest0_suf
          (optPolyEncoderBound_mono hbound hrest0_le) hres0 (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm]) (by simp only [arm64_norm, hspm]) (by simp only [arm64_norm, htrm])
          (by simp only [arm64_norm, hx19_m]) (by simp only [arm64_norm, hx20_m]) (by simp only [arm64_norm]) (by simp only [arm64_norm, hsm1, hsub]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm, hx27_m], by simp only [arm64_norm, hx28_m], by simp only [arm64_norm, hvregs_m]⟩
  · have hbeq := wt_beq_two_of_ne_lengthDelimited h_1 hwt_ld
    have hbne1 : (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 != 2#32) = true := by
      simp only [bne, hbeq, Bool.not_false]
    have hbne2 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5))) &&& 255#64) != 2#32) = true := by
      rw [BytesMergeFacts.truncate32_zeroExtend64_and_255_eq, h_1]; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | decide
    have hbne3 : (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) != 2#32) = true := by
      rw [show BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32)) =
            BitVec.truncate 32 (s0.readReg64 (Reg.gpr 0#5)) &&& 255#32 by bv_bits]; exact hbne1
    have hnone : (Proto.mergeMessage V1State.Chunked.EkReceivedCt1Sampled.mergeField (codecWireTypeToProto x.wt) x.msg x.bs 99).toOption = none := by
      rw [← mergeMessageBin_eq_proto_mergeMessage protoPrefixStep_chunked_ekReceivedCt1Sampled_mergeField]
      unfold mergeMessageBin; revert hwt_ld; cases x.wt <;> intro hwt_ld <;> first | contradiction | rfl
    apply SepWPpLscro.of_sepWP (mid := (blkPl_310).base + 120#64)
    conv => arg 4; rw [stackAt_chunkedInl_prologue s0.sp, sliceCursorAt, memRegion_48_wtErr160 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]; apply SepWP.exists_elim; intro v0; apply SepWP.exists_elim; intro v1; apply SepWP.exists_elim; intro v2
    apply SepWP.exists_elim; intro v3; apply SepWP.exists_elim; intro v4; apply SepWP.exists_elim; intro v5; apply SepWP.exists_elim; intro v6; apply SepWP.exists_elim; intro v7; apply SepWP.exists_elim; intro v8; apply SepWP.exists_elim; intro v9; apply SepWP.exists_elim; intro b_wt1
    apply SepWP.exists_elim; intro b_wt0; apply SepWP.exists_elim; intro v_wt0; wp_steps; apply SepWP.fold hsaved (by sep_focus); apply SepWP.fold (wtErr160_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 x.slot x.ptr (BitVec.ofNat 64 x.bs.length)) (by sep_focus); apply SepWP.fold (chunkedEkReceivedCt1SampledPBCapAt_entails_pb A x.msgPtr x.bs.length x.msg) (by sep_focus); wp_reach
    apply SepWPpLscro.weaken_pre (P' := ((s0.sp - 128#64) ↦₆₄ 0x8000000000000006#64) ∗ memRegion (s0.sp - 120#64) 40 ∗ stackAt (s0.sp - 128#64) chunkedInlBelowStack ∗ chunkedEkReceivedCt1SampledErrFrame A s0 x.msgPtr x.bufRef x.slot x.ptr x.msg x.bs)
      (by dsimp only [chunkedEkReceivedCt1SampledErrFrame]; sep_entail)
    exact hfrom_err hnone (by decide : KindNoHeap 0x8000000000000006#64) hsp_align (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun]) (by simp only [arm64_norm]) (by simp only [arm64_norm]) ⟨by simp only [arm64_norm], by simp only [arm64_norm]⟩


alias chunkedEkReceivedCt1Sampled_merge_cl_placed_ok_of_contracts := chunked_ek_received_ct1_sampled_merge_cl_placed_ok_of_contracts

end CryptoVerification.SpqrV1.Prost.MessageMerge
