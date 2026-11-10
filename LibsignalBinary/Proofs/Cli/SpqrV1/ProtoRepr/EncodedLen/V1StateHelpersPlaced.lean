/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Placed
import ProofLib.SepLogic.WPp

/-!
# Relocatable Helpers, Tails, and Single-Callee Branches for `V1State::encoded_len` (Block `484`)

Defines instruction-fetch macros and `BL` call bridges, and proves prologue, shared epilogue tails,
and single-callee variant branches (`k = 0, 2, 7`) on CLI Block `484` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open EncodedLen
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Block `484` Instruction Fetch Macro and `BL` Call Bridges -/

open Lean Elab Tactic in
elab "v1State_484_fetches_range " H:term:max kStart:num kEnd:num : tactic => do
  let skip : Array Nat := #[
    56, 60,
    124, 188, 260, 324, 376, 408, 472, 520, 600, 664,
    756, 820, 912, 976, 1024, 1076, 1140, 1192, 1256,
    1332, 1336, 1340, 1372, 1376, 1380, 1412, 1416, 1420,
    1452, 1456, 1460, 1492, 1496, 1500, 1532, 1536, 1540,
    1556, 1560, 1564, 1620, 1624, 1628, 1632, 1636, 1640
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    if !skip.contains k then
      if k == 0 then
        let fetchId := mkIdent (`CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced.blkPC_484_rebase_fetch_base)
        evalTactic (← `(tactic| have := $fetchId (blkPl_484).base $H))
      else
        let hexStr := String.ofList (Nat.toDigits 16 k)
        let fetchId := mkIdent (`CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced |>.str
          s!"blkPC_484_rebase_fetch_0x{hexStr}")
        evalTactic (← `(tactic| have := $fetchId (blkPl_484).base $H))

local macro "v1State_484_bl_plain " k:num calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_plain (k := $k) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (by simp only [arm64_norm]; rfl)
      (by first | simp only [arm64_norm] | (rw [bl_reloc_target_eq]; simp only [arm64_norm]))
      ($calleeOk $A $H))

local macro "v1State_484_bl_lscl " k:num calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_lscl (k := $k) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (by simp only [arm64_norm]; rfl)
      (by first | simp only [arm64_norm] | (rw [bl_reloc_target_eq]; simp only [arm64_norm]))
      ($calleeOk $A $H))

theorem v1State_484_bl_ku [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 1024
    CryptoVerification.Cli.SpqrV1.ProtoRepr.keysUnsampledEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ks1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 600
    CryptoVerification.Cli.SpqrV1.ProtoRepr.headerSentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ks2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 664
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack :=
  v1State_484_bl_lscl 376
    CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 408
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 472
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_escr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 124
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_escr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 188
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_nhr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 1076
    CryptoVerification.Cli.SpqrV1.ProtoRepr.noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_nhr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 1140
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 756
    CryptoVerification.Cli.SpqrV1.ProtoRepr.headerReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 820
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack :=
  v1State_484_bl_lscl 520
    CryptoVerification.Cli.SpqrV1.ProtoRepr.chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ercs1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 912
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ercs2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 976
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ca1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 260
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ct1SentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ca2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 324
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_c2s1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 1192
    CryptoVerification.Cli.SpqrV1.ProtoRepr.ct2SentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_c2s2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_plain 1256
    CryptoVerification.Cli.SpqrV1.ProtoRepr.polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 2. Shared Tails (`+524..+572` and `+1580..+1616 -> +564..+572`) -/

/-- Direct epilogue at `+524` (`0x20c`) of Block `484`. -/
theorem step_v1State_tail_524_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (H : String → Option (State → State))
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_484).base + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s P Q Qp := by
  v1State_484_fetches_range H 524 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Shared outer-varint + epilogue tail at `+1580` (`0x62c`) of Block `484`. -/
theorem step_v1State_tail_1580_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (H : String → Option (State → State))
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_484).base + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s P Q Qp := by
  v1State_484_fetches_range H 1580 1620
  v1State_484_fetches_range H 564 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-! ## 3. Single-Callee Variant Branches (`k = 0, 2, 7`) -/

/-- Branch `k = 0` (`keysUnsampled`, `+80`): steps from `(blkPl_484).base + 80#64` through `+1580` to `s0.readReg64 .lr`. -/
theorem step_v1State_keysUnsampled_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl : CallPinnedEncLenAtF Φ (lsProg_484 H) (blkPl_484).base 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (g : Unchunked2PBGhost) (a sp : BitVec 64) (v : V1State.Chunked.KeysUnsampled)
    (hfit : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_484).base + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : (optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
            (optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s P Q Qp := by
  v1State_484_fetches_range H 80 100
  v1State_484_fetches_range H 1028 1072
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap with ⟨hcap_beq, hcap_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_beq hcap_bne
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none]
    apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none, ← huc]
    refine step_v1State_tail_1580_placed Φ H sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, optKeysUnsampledPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_beq hcap_bne
    have hu_fit : keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optKeysUnsampledPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 1024#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u), ← huc]
    have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((keysUnsampledPBPinnedAt A g (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by
      simp only [huc, optKeysUnsampledPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl
    refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf_eq := bv_optMsgField_some (inner := keysUnsampledPBEncodedLen u)
      (tot := optKeysUnsampledPBFieldEncodedLen (some u)) rfl
    have htot_fit : optKeysUnsampledPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) <
        optKeysUnsampledPBFieldEncodedLen (some u) := by
      simp only [optKeysUnsampledPBFieldEncodedLen]; omega
    have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
    apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine step_v1State_tail_1580_placed Φ H sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hf_eq, hx0_1])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 2` (`headerSent`, `+372`) of Block `484`. -/
theorem step_v1State_headerSent_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl : CallPinnedEncLenAtF Φ (lsProg_484 H) (blkPl_484).base 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.HeaderSent)
    (hfit : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_484).base + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.headerSent v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s P Q Qp := by
  v1State_484_fetches_range H 372 384
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 376#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) v _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 524#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_524_placed Φ H sp (.headerSent v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, hx0_1])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 7` (`ct1Sampled`, `+520`) of Block `484`. -/
theorem step_v1State_ct1Sampled_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (A : RustAlloc) (H : String → Option (State → State))
    (hbl : CallPinnedEncLenAtF Φ (lsProg_484 H) (blkPl_484).base 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.Ct1Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_484).base + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedCt1SampledPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g a (sp - 32#64) v s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  refine step_v1State_tail_524_placed Φ H sp (.ct1Sampled v) hfit
    hpc1 hrun1 hsp1 halign (by simpa [v1StateInnerPayloadEncodedLen] using hx0_1)
    ⟨by simp [h20_1, h20], by simp [h21_1, h21], by simp [h22_1, h22],
     by simp [h23_1, h23], by simp [h24_1, h24], by simp [h25_1, h25],
     by simp [h26_1, h26], by simp [h27_1, h27], by simp [h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by rw [htrf, htr1]) hx0f hcsf

/-! ## 4. Prologue Symbolic Execution (`none` Path `+0..+36` and `some` Path `+0..+64`) -/

/-- Steps the `none` path (`+0..+36`) of Block `484` from `(blkPl_484).base` to `s0.readReg64 .lr`. -/
theorem step_v1State_none_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (H : String → Option (State → State))
    (a sp v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_484).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ noneCap2)))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ noneCap2))) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_484_fetches_range H 0 40
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_kernel
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Steps the `some` prologue (`+0..+64`) of Block `484` up to the jump-table `ADR X10, #16`. -/
theorem step_v1State_prologue_to_64_placed [LibsignalPlacement] (Φ : Memory → Prop) [FrozenInv Φ]
    (H : String → Option (State → State))
    (a sp w v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_484).base) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ w)))
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (blkPl_484).base + 64#64 → s1.status = .Running → s1.sp = sp - 32#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = a →
      s1.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      s1.readReg64 .x9 = lsρ CryptoVerification.Cli.SpqrV1.ProtoRepr.cliV1StateJtSym →
      (s1.readReg64 .x19 = s0.readReg64 .x19 ∧ V1CalleeSaved20To28 s1 s0) →
      P1 = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ w)) →
      SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s1 P1 Q Qp) :
    SepWPpF Φ (lsProg_484 H) (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_484_fetches_range H 0 56
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    rw [hsp]; clear *- halign; bv_kernel
  apply SepWPpF.of_sepWP (mid := (blkPl_484).base + 64#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx0])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm]⟩
    rfl

end CryptoVerification.SpqrV1.ProtoRepr
