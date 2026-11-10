/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
import ProofLib.SepLogic.WP.StateNorm
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs -- shake: keep

/-!
# Block `486` (`chunked::Ct1Sampled::encoded_len [local#3]`) Bridge on `v1State484Blocks`

Auxiliary module for `V1StatePlacedBudget` exporting `ct1Sampled_486_blocks_ok` over
`withLsBlocksCodeLoaded v1State484Blocks lsmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux2

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSpqrV1 (V1State PolynomialEncoder)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (lsProg_486 blkPl_486)
open CryptoVerification.SpqrV1.ProtoRepr
  (PinnedEncLenGhost FrozenInv SepWPpF CallPinnedEncLenAtF
   ChunkedCt1SampledPBGhost chunkedCt1SampledPBEncodedLen chunkedCt1SampledUnpacked
   chunkedCt1SampledPBPinnedAt_eq_unpacked chunkedCt1SampledUnpacked_bounds
   polynomialDecoderPBPinnedAt polynomialDecoderPBEncodedLen
   optPolynomialDecoderPBPinnedAt optPolynomialDecoderPBPinnedAt_eq
   optPolynomialDecoderPBFieldEncodedLen optPolyDecCap optPolyDecRest
   polynomialEncoderPBPinnedAt polynomialEncoderPBEncodedLen
   optPolynomialEncoderPBPinnedAt optPolynomialEncoderPBPinnedAt_eq
   optPolynomialEncoderPBFieldEncodedLen optPolyEncCap optPolyEncRest
   polyEncodedLenStack stackAt_chunkedEncodedLen_eq
   ct1SentPBPinnedAt ct1SentPBEncodedLen
   optCt1SentPBPinnedAt optCt1SentPBPinnedAt_eq
   optCt1SentPBFieldEncodedLen optCt1SentCap optCt1SentRest
   varintLen bv_optMsgField_some)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
   hwVarintLen_eq_ofNat_varintLen_norm hwVarintLen_bvShift_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
   cmp_ls_false_of_lt adds_no_overflow_of_eq)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (subroutine_ok_of_withVmPreserved LsBlocksCodeLoaded withLsBlocksCodeLoaded)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget
  (v1State484Blocks subroutine_ok_of_sepWPpF_blocks callPinnedEncLenAtF_of_bl_blocks)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
  (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x
   polynomialDecoderEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
  (ct1SentEncodedLen_local1_pinned_placed_ok_x)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## Block `486` Symbolic Execution (`SepWPpF`) -/

private theorem step_ct1Sampled_f3_ret_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl3 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (hdec_beq : (optPolyDecCap g.receivingEk m.receivingEk + 1#64 == 0#64) = !m.receivingEk.isSome)
    (hdec_bne : (optPolyDecCap g.receivingEk m.receivingEk + 1#64 != 0#64) = m.receivingEk.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64
      (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
           calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (chunkedCt1SampledPBEncodedLen m) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_486 H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases hrec : m.receivingEk with
  | none =>
    simp only [hrec, Option.isSome_none, Bool.not_false] at hdec_beq hdec_bne
    have htot_eq : optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1 =
        chunkedCt1SampledPBEncodedLen m := by
      unfold chunkedCt1SampledPBEncodedLen
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen, Nat.add_zero]
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)
  | some dec =>
    simp only [hrec, Option.isSome_some, Bool.not_true] at hdec_beq hdec_bne
    have hdec_fit : polynomialDecoderPBEncodedLen dec < 2 ^ 64 := by
      unfold chunkedCt1SampledPBEncodedLen at hfit
      simp only [hrec, optPolynomialDecoderPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 192#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    have hP_bl : ((((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
        ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
        optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
      ((polynomialDecoderPBPinnedAt A g.receivingEk (a + 184#64) dec ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
          ((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
          optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
          ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
      have hopt := optPolynomialDecoderPBPinnedAt_eq A g.receivingEk (a + 184#64) (some dec)
      simp only [optPolynomialDecoderPBPinnedAt] at hopt
      rw [hrec, hopt]
      sep_ac_rfl
    apply SepWPpF.congr_pre hP_bl
    refine hbl3 (s0.readReg64 .lr) g.receivingEk (a + 184#64) (sp - 32#64) dec _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
      (by simp_all) hdec_fit ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
    apply SepWPpF.congr_pre hP_bl.symm
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
    have hf3_eq := bv_optMsgField_some (inner := polynomialDecoderPBEncodedLen dec)
      (tot := optPolynomialDecoderPBFieldEncodedLen (some dec)) rfl
    have htot_fit : optPolynomialDecoderPBFieldEncodedLen (some dec) < 2 ^ 64 := by
      unfold chunkedCt1SampledPBEncodedLen at hfit
      simp only [hrec] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialDecoderPBEncodedLen dec)) <
        optPolynomialDecoderPBFieldEncodedLen (some dec) := by
      simp only [optPolynomialDecoderPBFieldEncodedLen]; omega
    have ⟨hule_f3, hule_f3_rev, hult_f3, hsub_f3, hbeq_f3⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have ⟨hadd_tot, hult_tot, hule_tot, _, _⟩ :=
      adds_no_overflow_of_eq
        (a := optPolynomialDecoderPBFieldEncodedLen (some dec))
        (b := optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1)
        (c := chunkedCt1SampledPBEncodedLen m)
        (by unfold chunkedCt1SampledPBEncodedLen; simp only [hrec])
        hfit
    apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    apply SepWPpF.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by epochEncLen_cc_close)

private theorem step_ct1Sampled_f2_some_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl2 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (enc : PolynomialEncoder) (henc : m.sendingCt1 = some enc)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base + 92#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a + 128#64)
    (hx19 : s.readReg64 .x19 = a)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc))
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
           calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_486).base + 176#64 →
      sf.status = .Running →
      sf.sp = sp - 32#64 →
      sf.trace = s.trace →
      sf.readReg64 .x19 = a →
      sf.readReg64 .x20 = BitVec.ofNat 64
        (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1) →
      (sf.readReg64 .x21 = s0.readReg64 .x21 ∧ sf.readReg64 .x22 = s0.readReg64 .x22 ∧
       sf.readReg64 .x23 = s0.readReg64 .x23 ∧ sf.readReg64 .x24 = s0.readReg64 .x24 ∧
       sf.readReg64 .x25 = s0.readReg64 .x25 ∧ sf.readReg64 .x26 = s0.readReg64 .x26 ∧
       sf.readReg64 .x27 = s0.readReg64 .x27 ∧ sf.readReg64 .x28 = s0.readReg64 .x28 ∧
       calleeSavedVRegs sf = calleeSavedVRegs s0) →
      SepWPpF Φ (lsProg_486 H) ret sf P Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s P Q Qp := by
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have henc_fit : polynomialEncoderPBEncodedLen enc < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [henc, optPolynomialEncoderPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((polynomialEncoderPBPinnedAt A g.sendingCt1 (a + 128#64) enc ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      (((a ↦₆₄ optCt1SentCap g.uc m.uc) ∗ optCt1SentRest A g.uc a m.uc ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedCt1SampledUnpacked
    have hopt := optPolynomialEncoderPBPinnedAt_eq A g.sendingCt1 (a + 128#64) (some enc)
    simp only [optPolynomialEncoderPBPinnedAt] at hopt
    rw [henc, hopt]
    sep_ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl2 ret g.sendingCt1 (a + 128#64) (sp - 32#64) enc s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 henc_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  have hf2_eq := bv_optMsgField_some (inner := polynomialEncoderPBEncodedLen enc)
    (tot := optPolynomialEncoderPBFieldEncodedLen (some enc)) rfl
  have htot_fit : optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [henc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen enc)) <
      optPolynomialEncoderPBFieldEncodedLen (some enc) := by
    simp only [optPolynomialEncoderPBFieldEncodedLen]; omega
  have ⟨hule_f2, hule_f2_rev, hult_f2, hsub_f2, hbeq_f2⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  have h12_fit : optCt1SentPBFieldEncodedLen m.uc +
      optPolynomialEncoderPBFieldEncodedLen (some enc) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit; simp only [henc] at hfit; omega
  have ⟨hadd_12, hult_12, hule_12, _, _⟩ :=
    adds_no_overflow_of_eq
      (a := optPolynomialEncoderPBFieldEncodedLen (some enc))
      (b := optCt1SentPBFieldEncodedLen m.uc)
      (c := optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen (some enc))
      (by omega)
      h12_fit
  unfold chunkedCt1SampledUnpacked
  apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 176#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1])
    (by simp [arm64_norm, htr1]) (by simp [arm64_norm, h19_1, hx19])
    (by simp [arm64_norm, henc, hadd_12, hf2_eq, h20_1, hx20, hx0_1])
    ⟨by simp [arm64_norm, h21_1, h21], by simp [arm64_norm, h22_1, h22],
     by simp [arm64_norm, h23_1, h23], by simp [arm64_norm, h24_1, h24],
     by simp [arm64_norm, h25_1, h25], by simp [arm64_norm, h26_1, h26],
     by simp [arm64_norm, h27_1, h27], by simp [arm64_norm, h28_1, h28]⟩

private theorem step_ct1Sampled_prologue_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (g : ChunkedCt1SampledPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc_beq : (optCt1SentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optCt1SentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.uc.isSome then (blkPl_486).base + 28#64 else (blkPl_486).base + 148#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s.trace →
      sm.readReg64 .x19 = a →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
       calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ (lsProg_486 H) ret sm
        ((chunkedCt1SampledUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s P Q Qp := by
  subst hP
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at huc_beq huc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 148#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at huc_beq huc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 28#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, huc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm]) (by simp [arm64_norm, hx0])
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩

private theorem step_ct1Sampled_f1_none_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc : m.uc = none)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base + 148#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
           calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then (blkPl_486).base + 92#64 else (blkPl_486).base + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧
       calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ (lsProg_486 H) ret sm P Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s P Q Qp := by
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optCt1SentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun])
      (by simp [arm64_norm, hsp]) (by simp [arm64_norm, htr])
      (by intro _; simp [arm64_norm, hx19]) (by simp [arm64_norm, hx19])
      (by simp [arm64_norm, huc, optCt1SentPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24],
       by simp [arm64_norm, h25], by simp [arm64_norm, h26],
       by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩

private theorem step_ct1Sampled_f1_some_post_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (u : V1State.Unchunked.Ct1Sent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s2 : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc2 : s2.pc = (blkPl_486).base + 36#64) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = sp - 32#64) (htr2 : s2.trace = s0.trace)
    (hx0_2 : s2.readReg64 .x0 = BitVec.ofNat 64 (ct1SentPBEncodedLen u))
    (h19_2 : s2.readReg64 .x19 = a)
    (hcs2 : s2.readReg64 .x21 = s0.readReg64 .x21 ∧ s2.readReg64 .x22 = s0.readReg64 .x22 ∧
            s2.readReg64 .x23 = s0.readReg64 .x23 ∧ s2.readReg64 .x24 = s0.readReg64 .x24 ∧
            s2.readReg64 .x25 = s0.readReg64 .x25 ∧ s2.readReg64 .x26 = s0.readReg64 .x26 ∧
            s2.readReg64 .x27 = s0.readReg64 .x27 ∧ s2.readReg64 .x28 = s0.readReg64 .x28 ∧
            calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then (blkPl_486).base + 92#64 else (blkPl_486).base + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧
       calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ (lsProg_486 H) ret sm P Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s2 P Q Qp := by
  rcases hcs2 with ⟨h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  subst hP
  have hf1_eq := bv_optMsgField_some (inner := ct1SentPBEncodedLen u)
    (tot := optCt1SentPBFieldEncodedLen (some u)) rfl
  have htot_fit : optCt1SentPBFieldEncodedLen (some u) < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [huc] at hfit; omega
  have hvlen_lt : varintLen (BitVec.ofNat 64 (ct1SentPBEncodedLen u)) <
      optCt1SentPBFieldEncodedLen (some u) := by
    simp only [optCt1SentPBFieldEncodedLen]; omega
  have ⟨hule_f1, hule_f1_rev, hult_f1, hsub_f1, hbeq_f1⟩ :=
    cmp_ls_false_of_lt hvlen_lt htot_fit
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.not_false] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 176#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro h; simp [henc] at h) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩
  | some enc =>
    simp only [henc, Option.isSome_some, Bool.not_true] at henc_beq henc_bne
    unfold chunkedCt1SampledUnpacked
    apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 92#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp [arm64_norm, henc]) (by simp [arm64_norm, hrun2])
      (by simp [arm64_norm, hsp2]) (by simp [arm64_norm, htr2])
      (by intro _; simp [arm64_norm, h19_2]) (by simp [arm64_norm, h19_2])
      (by simp [arm64_norm, huc, hf1_eq, hx0_2])
      ⟨by simp [arm64_norm, h21_2], by simp [arm64_norm, h22_2],
       by simp [arm64_norm, h23_2], by simp [arm64_norm, h24_2],
       by simp [arm64_norm, h25_2], by simp [arm64_norm, h26_2],
       by simp [arm64_norm, h27_2], by simp [arm64_norm, h28_2]⟩

private theorem step_ct1Sampled_f1_some_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl1 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (u : V1State.Unchunked.Ct1Sent) (huc : m.uc = some u)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base + 28#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64) (htr : s.trace = s0.trace)
    (halign : sp &&& 15#64 = 0#64) (hx19 : s.readReg64 .x19 = a)
    (hcs : s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
           s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
           s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
           s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
           calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then (blkPl_486).base + 92#64 else (blkPl_486).base + 176#64) →
      sm.status = .Running → sm.sp = sp - 32#64 → sm.trace = s0.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s0.readReg64 .x21 ∧ sm.readReg64 .x22 = s0.readReg64 .x22 ∧
       sm.readReg64 .x23 = s0.readReg64 .x23 ∧ sm.readReg64 .x24 = s0.readReg64 .x24 ∧
       sm.readReg64 .x25 = s0.readReg64 .x25 ∧ sm.readReg64 .x26 = s0.readReg64 .x26 ∧
       sm.readReg64 .x27 = s0.readReg64 .x27 ∧ sm.readReg64 .x28 = s0.readReg64 .x28 ∧
       calleeSavedVRegs sm = calleeSavedVRegs s0) →
      SepWPpF Φ (lsProg_486 H) ret sm P Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s P Q Qp := by
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hu_fit : ct1SentPBEncodedLen u < 2 ^ 64 := by
    unfold chunkedCt1SampledPBEncodedLen at hfit
    simp only [huc, optCt1SentPBFieldEncodedLen] at hfit
    omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : ((chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) =
    ((ct1SentPBPinnedAt A g.uc a u ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗
      ((((a + 128#64) ↦₆₄ optPolyEncCap g.sendingCt1 m.sendingCt1) ∗
        optPolyEncRest A g.sendingCt1 (a + 128#64) m.sendingCt1 ∗
        ((a + 184#64) ↦₆₄ optPolyDecCap g.receivingEk m.receivingEk) ∗
        optPolyDecRest A g.receivingEk (a + 184#64) m.receivingEk ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗ F)) := by
    unfold chunkedCt1SampledUnpacked
    have hopt := optCt1SentPBPinnedAt_eq A g.uc a (some u)
    simp only [optCt1SentPBPinnedAt] at hopt
    rw [huc, hopt]
    sep_ac_rfl
  apply SepWPpF.of_sepWP (mid := (blkPl_486).base + 32#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.congr_pre hP_bl
  refine hbl1 ret g.uc a (sp - 32#64) u _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align
    (by simp_all) hu_fit ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hcs2 hfp2
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2⟩
  exact step_ct1Sampled_f1_some_post_placed Φ A H g a sp m u huc
    henc_beq henc_bne hfit hpc2 hrun2 hsp2 (by simp_all) hx0_2 (by simp_all)
    ⟨by simp_all, by simp_all, by simp_all, by simp_all,
     by simp_all, by simp_all, by simp_all, by simp_all⟩ rfl hnext

private theorem step_ct1Sampled_f1_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl1 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp v32 v24 v16 v8 : BitVec 64) (m : V1State.Chunked.Ct1Sampled)
    (huc_beq : (optCt1SentCap g.uc m.uc + 1#64 == 0#64) = !m.uc.isSome)
    (huc_bne : (optCt1SentCap g.uc m.uc + 1#64 != 0#64) = m.uc.isSome)
    (henc_beq : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 == 0#64) = !m.sendingCt1.isSome)
    (henc_bne : (optPolyEncCap g.sendingCt1 m.sendingCt1 + 1#64 != 0#64) = m.sendingCt1.isSome)
    (hfit : chunkedCt1SampledPBEncodedLen m < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_486).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (chunkedCt1SampledUnpacked A g a m ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      stackAt (sp - 32#64) polyEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.sendingCt1.isSome then (blkPl_486).base + 92#64 else (blkPl_486).base + 176#64) →
      sm.status = .Running →
      sm.sp = sp - 32#64 →
      sm.trace = s.trace →
      (m.sendingCt1.isSome = true → sm.readReg64 .x0 = a + 128#64) →
      sm.readReg64 .x19 = a →
      sm.readReg64 .x20 = BitVec.ofNat 64 (optCt1SentPBFieldEncodedLen m.uc) →
      (sm.readReg64 .x21 = s.readReg64 .x21 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
       sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
       sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
       sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
       calleeSavedVRegs sm = calleeSavedVRegs s) →
      SepWPpF Φ (lsProg_486 H) ret sm
        ((chunkedCt1SampledUnpacked A g a m ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          stackAt (sp - 32#64) polyEncodedLenStack) ∗ F) Q Qp) :
    SepWPpF Φ (lsProg_486 H) ret s P Q Qp := by
  refine step_ct1Sampled_prologue_placed Φ A H g a sp v32 v24 v16 v8 m
    huc_beq huc_bne hpc hrun hsp halign hx0 hP ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hcs1
  cases huc : m.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact step_ct1Sampled_f1_none_placed Φ A H g a sp m huc
      henc_beq henc_bne hpc1 hrun1 hsp1 htr1 hx19_1 hcs1 rfl hnext
  | some u =>
    simp only [huc, Option.isSome_some, ↓reduceIte] at hpc1
    exact step_ct1Sampled_f1_some_placed Φ A H hbl1 g a sp m u huc
      henc_beq henc_bne hfit hpc1 hrun1 hsp1 htr1 halign hx19_1 hcs1 rfl hnext

private theorem ct1Sampled_486_pinned_wp [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl1 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 32
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack)
    (hbl2 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 92
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack)
    (hbl3 : CallPinnedEncLenAtF Φ (lsProg_486 H) (blkPl_486).base 192
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack) :
    ∀ (x : PinnedEncLenGhost ChunkedCt1SampledPBGhost V1State.Chunked.Ct1Sampled)
      (R : SepProp) (s0 : State), s0.pc = (blkPl_486).base → s0.status = .Running →
      (s0.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A).pre x s0 ∗ R) →
      s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF Φ (lsProg_486 H) (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f =>
            ((sf.mem ⊨ P_f ∗ Fr) →
              (sf.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A).post x s0 sf ∗ R)) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f =>
            (sf.mem ⊨ P_f ∗ Fr) →
              (sf.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A).onPanic x s0 sf ∗ R)) := by
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec,
    chunkedCt1SampledPBPinnedAt_eq_unpacked,
    stackAt_chunkedEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  have ⟨⟨huc_beq, huc_bne⟩, ⟨henc_beq, henc_bne⟩, ⟨hdec_beq, hdec_bne⟩⟩ :=
    chunkedCt1SampledUnpacked_bounds hpre
  refine ⟨(chunkedCt1SampledUnpacked A g a m ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) polyEncodedLenStack) ∗ R, emp,
      by rw [sepConj_emp]; convert hpre using 1; sep_ac_rfl, ?_⟩
  refine step_ct1Sampled_f1_placed (F := R) Φ A H hbl1 g a s0.sp v32 v24 v16 v8 m
    huc_beq huc_bne henc_beq henc_bne hfit hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1
  cases henc : m.sendingCt1 with
  | none =>
    simp only [henc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hx20_1' : s1.readReg64 .x20 = BitVec.ofNat 64
        (optCt1SentPBFieldEncodedLen m.uc + optPolynomialEncoderPBFieldEncodedLen m.sendingCt1) := by
      simp only [henc, optPolynomialEncoderPBFieldEncodedLen, Nat.add_zero, hx20_1]
    refine step_ct1Sampled_f3_ret_placed (F := R) Φ A H hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc1 hrun1 hsp1 halign hx19_1 hx20_1' hcs1 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec,
      chunkedCt1SampledPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr1]⟩, ?_⟩
    convert hm_f using 1; sep_ac_rfl
  | some enc =>
    simp only [henc, Option.isSome_some, ↓reduceIte, forall_const] at hpc1 hx0_1
    refine step_ct1Sampled_f2_some_placed (F := R) Φ A H hbl2 g a s0.sp m enc henc hfit
      hpc1 hrun1 hsp1 halign hx0_1 hx19_1 hx20_1 hcs1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2
    refine step_ct1Sampled_f3_ret_placed (F := R) Φ A H hbl3 g a s0.sp m
      hdec_beq hdec_bne hfit hpc2 hrun2 hsp2 halign hx19_2 hx20_2 hcs2 rfl ?_
    intro sf hpcf hrunf hspf htrf hx0_f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f; rw [sepConj_emp] at hm_f
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec,
      chunkedCt1SampledPBPinnedAt_eq_unpacked,
      stackAt_chunkedEncodedLen_eq,
      sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x20, s0.readReg64 .x19,
      ⟨hx0_f, by rw [htrf, htr2, htr1]⟩, ?_⟩
    convert hm_f using 1; sep_ac_rfl

/-- Block `486` (`chunked::Ct1Sampled::encoded_len [local#3]`) over `v1State484Blocks`. -/
theorem ct1Sampled_486_blocks_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_486 H) (blkPl_486).base
      (withLsBlocksCodeLoaded v1State484Blocks lsmpl
        (CryptoVerification.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLenPinnedSpec A)) := by
  refine subroutine_ok_of_sepWPpF_blocks ?_
  refine ct1Sampled_486_pinned_wp (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks (blks := v1State484Blocks) (k := 32)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (ct1SentEncodedLen_local1_pinned_placed_ok_x A H))
  · exact callPinnedEncLenAtF_of_bl_blocks (blks := v1State484Blocks) (k := 92)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H))
  · exact callPinnedEncLenAtF_of_bl_blocks (blks := v1State484Blocks) (k := 192)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H))

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux2
