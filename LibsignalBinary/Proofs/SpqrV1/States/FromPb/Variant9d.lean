/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9c
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPb
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 9 (`Ct1Acknowledged`, `+444`) — Part D

Pure model reductions, `<PolyDecoder>::from_pb` setup and post-call staging (`+2864 -> +3040`,
`+3044 -> +8588 | +8180`), and exit-tail compositions (`+5368`, `+5360`, `+6904`, `+8588`, `+3044 -> s0.x30`)
for `InnerState.ct1Acknowledged`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

theorem v9_sub_ok_ct1_sent_from_pb
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 15272#64)
      (ct1SentFromPbSpec A F) :=
  sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 15272) (b := b) (X := Rust.withPanics ext)
      statesFromPb_fnOff fnOff_ct1_sent_from_pb (by decide))
    (ct1_sent_from_pb_ok_ext (b := b) (A := A) (F := F) (ext := ext) hA)

/-! ## 1. Pure Model Reduction Lemmas for `Ct1Acknowledged::from_pb` -/

theorem v9_ptsNeeded_toNat_bne_576_eq (w : BitVec 32) :
    (w.toNat != ENCAPSULATION_KEY_SIZE / 2) = !(w == 576#32) := by
  change (w.toNat != 576) = !(w == 576#32)
  by_cases h : w = 576#32
  · subst h; rfl
  · have hne : w.toNat ≠ 576 := by
      intro heq
      apply h
      apply BitVec.eq_of_toNat_eq
      exact heq
    have hb1 : (w.toNat != 576) = true := bne_iff_ne.mpr hne
    have hb2 : (w == 576#32) = false := beq_false_of_ne h
    rw [hb1, hb2]; rfl

theorem v9_states_from_pb_ct1Acknowledged_ptsNeeded_ne {F : ShaCompress}
    (uc : Option V1State.Unchunked.Ct1Sent) (d : PolynomialDecoder)
    (hne : (d.ptsNeeded == 576#32) = false) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := uc, receivingEk := some d }) } =
    .error (.err .msgDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, hne]
  rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_none_dec_none {F : ShaCompress} :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := none, receivingEk := none }) } =
    .error (.err .stateDecode) := rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_none_dec_some {F : ShaCompress}
    (d : PolynomialDecoder) (heq : (d.ptsNeeded == 576#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := none, receivingEk := some d }) } =
    .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, heq]
  rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_some_dec_none {F : ShaCompress}
    (u : V1State.Unchunked.Ct1Sent) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := none }) } =
    match Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
    | .ok _ => .error (.err .stateDecode)
    | .error e => .error e := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only [bind, Except.bind, Functor.map, Except.map]
  cases Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u <;> rfl

theorem v9_states_from_pb_ct1Acknowledged_uc_some_dec_some {F : ShaCompress}
    (u : V1State.Unchunked.Ct1Sent) (d : PolynomialDecoder)
    (heq : (d.ptsNeeded == 576#32) = true) :
    States.from_pb spqrPolyApi (spqrAuthApi F)
      { innerState := some (.ct1Acknowledged { uc := some u, receivingEk := some d }) } =
    match Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
    | .error e => .error e
    | .ok uc =>
      match decoderFromPbResult (pbToProtoPolyDecoder d) with
      | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := dec })
      | .error _ => .error (.err .stateDecode) := by
  unfold States.from_pb Chunked.SendCt.Ct1Acknowledged.from_pb
  dsimp only
  rw [v9_ptsNeeded_toNat_bne_576_eq d.ptsNeeded, heq]
  dsimp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  cases Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u with
  | error e => rfl
  | ok uc =>
    dsimp only
    rw [decoderFromPbStateDecode_some d]
    cases decoderFromPbResult (pbToProtoPolyDecoder d) <;> rfl

/-! ## 2. Stepping Lemmas for `+2864 -> +3040` and `+3044 -> +8588 | +8180` -/

section StepLemmas

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  v9_x25_add_209
  v9_x25_add_209_sext
  v9_pbA_add_145
  v9_x21_add_57
  v9_x21_add_57_sext
  v9_x24_add_9
  v9_x24_add_9_sext
  v9_x21_add_15
  v9_x21_add_15_sext
  v9_x21_add_39
  v9_x21_add_39_sext
  v9_fsp_add_247_sext
  v9_bv_add_add_lit

/-- At `+2864`, when `ct1SentFromPb` returned `Ok(uc)` (`rkCap.toNat < 2 ^ 63`) and
    `receivingEk = some d` (`decW0.toNat < 2 ^ 63`), spills `uc` fields to `fsp + 40..255`,
    copies `pbToProtoPolyDecoder d` to `fsp + 896..936`, and sets up `DecoderFromPbOkExt` at `+3040`. -/
theorem v9_step_2864_ok_some_to_3040
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (decW0 decW8 decW16 : BitVec 64) (decD24 decD28 : BitVec 32) (decW32 : BitVec 64) (d : PolynomialDecoder)
    (w40 w48 w56 w72 w80 w128 w136 w144 w152 w200 w216 w240 w248 : BitVec 64) (d96 : BitVec 32) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hrk_lt : rkCap.toNat < 2 ^ 63) (hdec_lt : decW0.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2864#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = decW8) (hx21 : s.readReg64 .x21 = decW0) (hx23 : s.readReg64 .x23 = decW32)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx27 : s.readReg64 .x27 = pbA) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64) s
      (((fsp + 40#64) ↦₆₄ w40) ∗ ((fsp + 48#64) ↦₆₄ w48) ∗ ((fsp + 56#64) ↦₆₄ w56) ∗
        ((fsp + 72#64) ↦₆₄ w72) ∗ ((fsp + 80#64) ↦₆₄ w80) ∗ ((fsp + 96#64) ↦₃₂ d96) ∗
        ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗ ((fsp + 144#64) ↦₆₄ w144) ∗
        ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 200#64) ↦₆₄ w200) ∗ ((fsp + 216#64) ↦₆₄ w216) ∗
        ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 248#64) ↦ₛ EncoderFromPb.loBytes7 w248) ∗
        memRegion (fsp + 896#64) 40 ∗
        v9_optProtoUcWordsAt (fsp + 1888#64) rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep ∗
        v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ protoPolynomialDecoderAt A (fsp + 896#64) (pbToProtoPolyDecoder d) ∗ memRegion (fsp + 1888#64) 128 ∗
          ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          v9_optProtoPolyDecoderWordsAt (pbA + 136#64) decW0 decW8 decW16 decD24 decD28 decW32 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = fsp + 1888#64 ∧ s1.readReg64 .x1 = fsp + 896#64 ∧
        s1.readReg64 .x19 = out ∧ s1.readReg64 .x21 = fsp + 848#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = esLen ∧
        s1.readReg64 .x26 = rkLen ∧ s1.readReg64 .x28 = rkPtr ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64 ∧
        TraceCalleeSaved s1 s0) := by
  subst hsp
  have hrk_ne : (rkCap + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hrk_lt)
  have hdec_ne : (decW0 + 1#64 == 0#64) = false := Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hdec_lt)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (v9_memRegion_896_40_split s.sp)))))))))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z32; apply ProofLib.SepWP.exists_left; intro z24
  apply ProofLib.SepWP.exists_left; intro z16; apply ProofLib.SepWP.exists_left; intro z8
  apply ProofLib.SepWP.exists_left; intro z0
  dsimp only [v9_optProtoUcWordsAt, v9_optProtoPolyDecoderWordsAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 2864 180
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  iterate 21 wp_step
  wp_conv_pre => rw [v9_fsp_2000_realign_rest s.sp ct1Len ep]
  wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_240_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w248,
        v9_fsp_2000_unrealign_rest s.sp ct1Len ep]
  iterate 3 wp_step
  wp_conv_pre => rw [v9_pbA_144_triple_rest pbA decW8 decW16 decD24 decD28]
  wp_step
  wp_conv_pre =>
    rw [← v9_pbA_144_triple_rest pbA decW8 decW16 decD24 decD28,
        v9_pbA_160_pair32_eq_64_rest pbA decD24 decD28]
  iterate 12 wp_step
  wp_conv_pre => rw [v9_fsp_904_triple_rest s.sp z8 z16 z24]
  wp_step; wp_step
  wp_conv_pre =>
    rw [v9_fsp_913_realign_rest s.sp
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24))) z24]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm1888 := v9_optProtoUcWordsAt_entails_128 (s.sp + 1888#64)
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep
    dsimp only [v9_optProtoUcWordsAt] at hm1888; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1888
    have hp32_160 := (v9_pointsTo32_pair_eq_pointsTo64 (pbA + 160#64) decD24 decD28).symm
    have ha164 : (pbA + 160#64) + 4#64 = pbA + 164#64 := by bv_omega
    rw [ha164] at hp32_160
    have hp32_920 := (v9_pointsTo32_pair_eq_pointsTo64 (s.sp + 920#64) decD24 decD28).symm
    have ha924 : (s.sp + 920#64) + 4#64 = s.sp + 924#64 := by bv_omega
    rw [ha924] at hp32_920
    have hlo_w8 : BitVec.zeroExtend 8 decW8 = EncoderFromPb.loByte decW8 := by
      unfold EncoderFromPb.loByte; bv_kernel
    have h904_comb :
        ((s.sp + 904#64) ↦₈ BitVec.zeroExtend 8 decW8) ∗
        ((s.sp + 905#64) ↦₆₄ EncoderFromPb.unshiftWord decW8 (EncoderFromPb.loByte decW16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24)))) ∗
        ((s.sp + 920#64) ↦₆₄ (decD28 ++ decD24)) =
        ((s.sp + 904#64) ↦₆₄ decW8) ∗ ((s.sp + 912#64) ↦₆₄ decW16) ∗
        ((s.sp + 920#64) ↦₃₂ decD24) ∗ ((s.sp + 924#64) ↦₃₂ decD28) := by
      rw [hlo_w8]
      have h1 := v9_dst24_realign_final (s.sp + 904#64) decW8 decW16 (decD28 ++ decD24)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1; rw [h1, hp32_920]
    have hpack := v9_protoPolyDecoderAt_pack A (s.sp + 896#64) (pbToProtoPolyDecoder d)
      decW0 decW8 decW16 decD24 decD28 decW32
    dsimp only [v9_optProtoPolyDecoderWordsAt] at hpack; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
    rw [hp32_160]
    refine Entails.trans (Entails.of_eq (show _ =
      (((s.sp + 896#64) ↦₆₄ decW0) ∗
       (((s.sp + 904#64) ↦₈ BitVec.zeroExtend 8 decW8) ∗
        ((s.sp + 905#64) ↦₆₄ EncoderFromPb.unshiftWord decW8 (EncoderFromPb.loByte decW16)) ∗
        ((s.sp + 913#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord decW16 (EncoderFromPb.loByte (decD28 ++ decD24)))) ∗
        ((s.sp + 920#64) ↦₆₄ (decD28 ++ decD24))) ∗
       ((s.sp + 928#64) ↦₆₄ decW32) ∗
       v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32) ∗
      ((((s.sp + 1888#64) ↦₆₄ rkCap) ∗ ((s.sp + 1896#64) ↦₆₄ rkPtr) ∗ ((s.sp + 1904#64) ↦₆₄ rkLen) ∗
        ((s.sp + 1912#64) ↦₆₄ mkCap) ∗ ((s.sp + 1920#64) ↦₆₄ mkPtr) ∗ ((s.sp + 1928#64) ↦₆₄ mkLen) ∗
        ((s.sp + 1936#64) ↦₆₄ hdrCap) ∗ ((s.sp + 1944#64) ↦₆₄ hdrPtr) ∗ ((s.sp + 1952#64) ↦₆₄ hdrLen) ∗
        ((s.sp + 1960#64) ↦₆₄ esCap) ∗ ((s.sp + 1968#64) ↦₆₄ esPtr) ∗ ((s.sp + 1976#64) ↦₆₄ esLen) ∗
        ((s.sp + 1984#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 1992#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 2000#64) ↦₆₄ ct1Len) ∗
        ((s.sp + 2008#64) ↦₆₄ ep)) ∗
       ((s.sp + 40#64) ↦₆₄ mkLen) ∗ ((s.sp + 48#64) ↦₆₄ ct1Cap) ∗ ((s.sp + 56#64) ↦₆₄ rkCap) ∗
       ((s.sp + 72#64) ↦₆₄ esPtr) ∗ ((s.sp + 80#64) ↦₆₄ hdrLen) ∗
       ((s.sp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
       ((s.sp + 128#64) ↦₆₄ esCap) ∗ ((s.sp + 136#64) ↦₆₄ mkPtr) ∗ ((s.sp + 144#64) ↦₆₄ hdrPtr) ∗
       ((s.sp + 152#64) ↦₆₄ hdrCap) ∗ ((s.sp + 200#64) ↦₆₄ ct1Ptr) ∗ ((s.sp + 216#64) ↦₆₄ mkCap) ∗
       ((s.sp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
       ((s.sp + 247#64) ↦₆₄ ep) ∗
       (((pbA + 136#64) ↦₆₄ decW0) ∗ ((pbA + 144#64) ↦₆₄ decW8) ∗ ((pbA + 152#64) ↦₆₄ decW16) ∗
        ((pbA + 160#64) ↦₃₂ decD24) ∗ ((pbA + 164#64) ↦₃₂ decD28) ∗ ((pbA + 168#64) ↦₆₄ decW32)) ∗ Rest) by ac_rfl)) ?_
    rw [h904_comb]
    have hpack' :
        ((s.sp + 896#64) ↦₆₄ decW0) ∗
        (((s.sp + 904#64) ↦₆₄ decW8) ∗ ((s.sp + 912#64) ↦₆₄ decW16) ∗
         ((s.sp + 920#64) ↦₃₂ decD24) ∗ ((s.sp + 924#64) ↦₃₂ decD28)) ∗
        ((s.sp + 928#64) ↦₆₄ decW32) ∗
        v9_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) decW0 decW8 decW16 decD24 decD28 decW32 ⊢
        protoPolynomialDecoderAt A (s.sp + 896#64) (pbToProtoPolyDecoder d) :=
      Entails.trans (Entails.of_eq (by ac_rfl)) hpack
    exact Entails.trans (sepConj_mono hpack' (sepConj_mono_left hm1888)) (Entails.of_eq (by ac_rfl))
  · wp_done

/-- At `+3044`, when `decoderFromPbResult pbDec = .error err` (`[fsp + 1888] = noneCap`),
    collapses `fsp + 1888..2288` into `memRegion (fsp + 1888#64) 400` and branches at `+3052`
    (`b.eq +8588`) to `+8588`. -/
theorem v9_step_3044_err_to_8588
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out rkPtr : BitVec 64) (err : PolynomialError) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ memRegion (fsp + 1888#64) 400 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x28 = rkPtr ∧ TraceCalleeSaved s1 s0) := by
  refine SepWP.weaken_pre (sepConj_mono_left (v9_resultPolyDecoder_err_entails_tag_392 A fsp err)) ?_
  wp_simp_pre [sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3044 12
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hm400 : ((fsp + 1888#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 1896#64) 392 ⊢
        memRegion (fsp + 1888#64) 400 := by
      rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
            (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
    rw [← sepConj_assoc]; exact sepConj_mono_left hm400
  · wp_done

/-- At `+3044`, when `decoderFromPbResult pbDec = .ok dec` (`(v9_wordAt bs 0).toNat < 2 ^ 63`),
    copies the `PolyDecoder` cells and `Ct1Sent` fields into the epilogue stack slots and
    registers and branches at `+3344` (`b +8180`) to `+8180`. -/
theorem v9_step_3044_ok_to_8180
    {b : BitVec 64} {ext : String → Option (State → State)} (s0 s : State) (fsp out : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len ep : BitVec 64)
    (w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 w2272 w2280 : BitVec 64) (d172 : BitVec 32)
    (q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 : BitVec 128)
    (bs : List (BitVec 8)) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (hw0_lt : (v9_wordAt bs 0).toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx21 : s.readReg64 .x21 = fsp + 848#64) (hx24 : s.readReg64 .x24 = fsp + 1888#64)
    (hx25 : s.readReg64 .x25 = esLen) (hx26 : s.readReg64 .x26 = rkLen)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64) s
      (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
        ((fsp + 247#64) ↦₆₄ ep) ∗
        ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
        ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
        ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
        ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
        ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
        ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
        ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
        v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
          ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
          ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ v9_wordAt bs 376) ∗ ((fsp + 112#64) ↦₆₄ w2272) ∗ ((fsp + 120#64) ↦₆₄ w2280) ∗
          ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
          ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs 312) ∗
          ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs 8)).zeroExtend 32) ∗
          ((fsp + 192#64) ↦₆₄ v9_wordAt bs 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
          ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs 344) ∗
          ((fsp + 232#64) ↦₆₄ v9_wordAt bs 296) ∗
          ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep))) ∗
          ((fsp + 247#64) ↦₆₄ ep) ∗
          ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs 48) ∗
          ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs 80) ∗
          ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs 112) ∗
          ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs 144) ∗
          ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs 176) ∗
          ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs 208) ∗
          ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs 240) ∗
          ((fsp + 832#64) ↦₆₄ v9_wordAt bs 256) ∗
          ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)) ∗
          ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs 24 >>> 8)) ∗
          ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ∗
          ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (ep >>> 8)) ∗
          v9_decCellsAt (fsp + 1888#64) bs ∗ ((fsp + 2272#64) ↦₆₄ w2272) ∗ ((fsp + 2280#64) ↦₆₄ w2280) ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x0 = esPtr ∧ s1.readReg64 .x1 = v9_wordAt bs 336 ∧
        s1.readReg64 .x2 = v9_wordAt bs 264 ∧ s1.readReg32 .x3 = esLen.extractLsb' 0 32 ∧
        s1.readReg64 .x4 = ct1Cap ∧ s1.readReg64 .x5 = ct1Ptr ∧ s1.readReg64 .x6 = fsp + 576#64 ∧
        s1.readReg64 .x7 = v9_wordAt bs 0 ∧ s1.readReg64 .x8 = 11#64 ∧ s1.readReg64 .x9 = hdrCap ∧
        s1.readReg64 .x10 = v9_wordAt bs 304 ∧ s1.readReg64 .x11 = v9_wordAt bs 272 ∧
        s1.readReg64 .x12 = v9_wordAt bs 328 ∧ s1.readReg64 .x13 = mkCap ∧
        s1.readReg64 .x14 = hdrPtr ∧ s1.readReg64 .x15 = rkCap ∧
        s1.readReg64 .x16 = v9_wordAt bs 368 ∧ s1.readReg64 .x17 = esCap ∧
        s1.readReg64 .x18 = hdrLen ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = rkLen ∧
        s1.readReg32 .x21 = (EncoderFromPb.loByte ct1Len).zeroExtend 32 ∧
        s1.readReg64 .x22 = v9_wordAt bs 280 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = v9_wordAt bs 288 ∧ s1.readReg64 .x25 = mkPtr ∧
        s1.readReg64 .x26 = v9_wordAt bs 320 ∧ s1.readReg64 .x27 = esLen >>> 8 ∧
        s1.readReg32 .x27 = (esLen >>> 8).extractLsb' 0 32 ∧
        s1.readReg64 .x28 = v9_wordAt bs 352 ∧ s1.readReg64 .x30 = mkLen ∧ TraceCalleeSaved s1 s0) := by
  subst hsp
  have hw0_ne : (v9_wordAt bs 0 + 1#64 == 0#64) = false :=
    Bool.eq_false_iff.mpr (cap_add_one_beq_zero_false hw0_lt)
  unfold v9_decCellsAt pointsTo128; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  states_from_pb_fetches_range b (Rust.withPanics ext) 3044 304
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches; iterate 3 wp_step
  wp_conv_pre => rw [v9_fsp_1896_realign_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)]
  wp_step
  wp_conv_pre =>
    rw [v9_fsp_1896_unrealign_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24),
        v9_fsp_1896_split_1_7_rest s.sp (v9_wordAt bs 8)]
  iterate 8 wp_step
  wp_conv_pre =>
    rw [v9_fsp_856_realign_rest s.sp
          ((v9_midQ128 (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)).extractLsb' 64 64) w864]
  wp_step
  wp_conv_pre => rw [v9_fsp_856_unrealign_midQ128_rest s.sp (v9_wordAt bs 8) (v9_wordAt bs 16) (v9_wordAt bs 24)]
  iterate 19 wp_step
  wp_conv_pre => rw [v9_fsp_240_realign_overlap_rest s.sp ct1Len ep]
  iterate 5 wp_step
  wp_conv_pre => rw [← v9_fsp_240_realign_overlap_rest s.sp ct1Len ep]
  iterate 8 wp_step
  wp_conv_pre =>
    rw [v9_fsp_880_realign_64_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) w888]
  wp_step
  wp_conv_pre =>
    rw [v9_fsp_880_realign_rest s.sp (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte ep)) ep,
        v9_overlapLow7_unshift ct1Len ep]
  wp_steps
  wp_conv_pre => rw [v9_fsp_1896_unsplit_1_7_rest s.sp (v9_wordAt bs 8)]
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

end StepLemmas

/-! ## 3. Composition Helpers & Exit Tails (`+5368`, `+5360`, `+6904`, `+8588`, `+8180`) -/

theorem v9_sepWPp_entails_to_satisfies {prog : Program} {ret : BitVec 64} {s : State}
    {P R : SepProp} {Q : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun sf Pf => Pf ⊢ statesFromPbOnPanic s sf)) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s sf ∗ R)) := by
  intro R' hm hL; obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  rcases hout with hok | ⟨hst, Pf, hmf, hPf⟩ | hoom
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf, hmf, fun hmR => Satisfies.mono (sepConj_mono_left hPf) hmR⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem v9_sepWPp_call_ret_entails {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α} (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hpre : P_step ⊢ spec.pre x s)
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf) (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp →
      CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post (fun sf P_f => P_f ⊢ Qpan sf) :=
  SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact Satisfies.mono (sepConj_mono_left hpre) hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (hoom := fun sf R' _ hm => by rw [hoom_eq] at hm; exact False.elim (not_satisfies_false_sepConj hm))
    (fun sf _ => hpan sf) (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))

theorem v9_sepWPp_frame_right {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P Post J : SepProp} {Regs : State → Prop}
    (h : SepWPp prog ret s P
      (fun sf Pf => (Pf ⊢ Post) ∧ Regs sf)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf)) :
    SepWPp prog ret s (P ∗ J)
      (fun sf Pf => (Pf ⊢ Post ∗ J) ∧ Regs sf)
      (fun sf Pf => Pf ⊢ statesFromPbOnPanic s0 sf) := by
  intro R' hm hL; rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, hout⟩ := h (J ∗ R') hm hL
  rcases hout with ⟨hpc, hrun, Pf, hmf, hPf, hregs⟩ | ⟨hst, Pf, hmf, hPf⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf ∗ J, hmf, sepConj_mono_left hPf, hregs⟩⟩
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, Pf ∗ J, hmf,
      Entails.trans (sepConj_mono_left hPf) (v9_onPanic_frame_entails ⟨rfl, rfl⟩)⟩)⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem v9_pbA_entails_224
    (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000009#64) ∗
      v9_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 u120 ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (v9_optProtoUcWordsAt_entails_128 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) <|
    collapse_step (v9_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v9_pbA_128_entails_224
    (pbA w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 : BitVec 64) :
    (pbA ↦₆₄ 0x8000000000000009#64) ∗
      memRegion (pbA + 8#64) 128 ∗
      v9_optProtoPolyDecoderWordsAt (pbA + 136#64) w0 w8 w16 d24 d28 w32 ∗
      memRegion (pbA + 176#64) 48 ⊢
      memRegion pbA optProtoInnerStateSize := by
  exact collapse_top <|
    collapse_step0 (Drop.pointsTo64_entails_memRegion _ _) <|
    collapse_step (Entails.refl _) <|
    collapse_step (v9_optProtoPolyDecoderWordsAt_entails_40 _ _ _ _ _ _ _) <|
    Entails.refl _

theorem v9_stackAt_encoderFromPbStack_eq_ct1SentFromPb (fsp : BitVec 64) :
    stackAt fsp encoderFromPbStack =
      stackAt fsp ct1SentFromPbStack ∗ memRegion (fsp - 5152#64) 816 := by
  rw [show encoderFromPbStack = ct1SentFromPbStack + 816 from rfl,
      ProofLib.stackAt_split_bottom fsp ct1SentFromPbStack 816 (by decide),
      sepConj_comm]

theorem v9_seq_err_7084
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State) (fsp out pbA : BitVec 64) (P : SepProp) (err : LibsignalSpqrV1.Error)
    {Q : State → Prop}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp_eq : fsp = s0.sp - 2400#64)
    (hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64) s P
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion (s0.sp - 2400#64) 2304 ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          (memRegion pbA optProtoInnerStateSize ∗ A.pool)) ∧
        Q sm))
    (hQ : ∀ sm, Q sm →
      sm.sp = fsp ∧ sm.readReg64 .x19 = out ∧
      (sm.readReg64 .x28).extractLsb' 0 8 = spqrErrorByte err ∧ TraceCalleeSaved sm s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          A.pool ∗
          stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7084#64)
    (P_mid := stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 2304 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool))
    (Q := Q) hstep ?_
  intro sm hpcm hrunm hq
  obtain ⟨hspm, hx19m, herr_m, htrm⟩ := hQ sm hq
  rw [hfsp_eq] at hspm
  refine SepWP.mono (v9_states_from_pb_err_7084 (A := A) (F := F) s0 sm out err
    (memRegion pbA optProtoInnerStateSize ∗ A.pool)
    hsp0_align hpcm hrunm hspm hx19m herr_m htrm) ?_
  intro sf Pf _ _ ⟨hPf, hrest⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hrest⟩

/-- From `+5368` (`dealloc_proto_decoder_5368`) through `+7084` (`err_7084`) to `s0.x30`
    when `receivingEk = some d` is still live in `v9_optProtoPolyDecoderHeap`. -/
theorem v9_tail_5368_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (d : ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5368#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A (some d) w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
      (Entails.of_eq (show _ =
        (if w0 = 0#64 then emp
         else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
           memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_dealloc_proto_decoder_5368 hA s0 s fsp out w8 w0 x28_val d.pts
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
         memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hle hcap hpc hrun hpres hx22))
    (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+5360` (`dealloc_none/some_proto_decoder_5360`) through `+7084` (`err_7084`) to `s0.x30`
    for arbitrary `optDec : Option ProtoPolynomialDecoder`. -/
theorem v9_tail_5360_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (w0 w8 w16 : BitVec 64) (d24 d28 : BitVec 32) (w32 x28_val : BitVec 64)
    (optDec : Option ProtoPolynomialDecoder) (err : LibsignalSpqrV1.Error)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 5360#64)
    (hrun : s.status = .Running)
    (hpres : v9_Saved5368Preserved s0 s fsp out w8 w0 x28_val)
    (hx22 : s.readReg64 .x22 = w16)
    (herr : x28_val.extractLsb' 0 8 = spqrErrorByte err) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (v9_optProtoPolyDecoderHeap A optDec w0 w8 w16 d24 d28 w32 ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err err)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases optDec with
  | none =>
    dsimp only [v9_optProtoPolyDecoderHeap]
    apply SepWP.pure_elim; rintro rfl
    refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_none_proto_decoder_5360 s0 s fsp out w8 x28_val
          (memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hpc hrun hpres))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq; exact Entails.of_eq (by ac_rfl)
  | some d =>
    dsimp only [v9_optProtoPolyDecoderHeap]; rw [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, hle, hcap, hp_ne, hw32⟩
    refine SepWP.weaken_pre
      (Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))))
        (Entails.of_eq (show _ =
          (if w0 = 0#64 then emp
           else A.live w8 (w0.toNat * 24) 8 ∗ arrayAt (fun bs addr => vecU8 A addr bs) 24 w8 d.pts ∗
             memRegion (w8 + BitVec.ofNat 64 (d.pts.length * 24)) ((w0.toNat - d.pts.length) * 24)) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine v9_seq_err_7084 s0 s fsp out pbA _ err hsp0_align hfsp_eq
      (SepWP.strengthen_entails_const ?_
        (v9_states_from_pb_dealloc_some_proto_decoder_5360 hA s0 s fsp out w8 w0 x28_val d.pts
          (memRegion (fsp - 5152#64) 1056 ∗ memRegion pbA optProtoInnerStateSize ∗
           memRegion fsp 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
          hfsp_align hle hcap hpc hrun hpres hx22))
      (fun sm ⟨hspm, hx19m, _, _, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m, herr], htrm⟩)
    subst hfsp_eq
    refine Entails.trans (Entails.of_eq (show _ =
      (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
      memRegion (s0.sp - 2400#64) 2304 ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
      (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
    exact sepConj_mono_left (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))

/-- From `+6904` (`drop_uc_6904`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_6904_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 6904#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = mkPtr) (hx1 : s.readReg64 .x1 = mkCap)
    (hx10 : s.readReg64 .x10 = rkCap) (hx13 : s.readReg64 .x13 = ct1Cap)
    (hx14 : s.readReg64 .x14 = ct1Ptr) (hx19 : s.readReg64 .x19 = out)
    (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion fsp 72 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗ memRegion (fsp + 80#64) 48 ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ memRegion (fsp + 136#64) 8 ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ memRegion (fsp + 160#64) 2144 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ A.pool ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
    vecCapPtrDealloc A hdrCap hdrPtr ∗ vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗
    A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_6904 hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 72 ∗ memRegion (fsp + 80#64) 48 ∗
         memRegion (fsp + 136#64) 8 ∗ memRegion (fsp + 160#64) 2144 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx0 hx1 hx10 hx13 hx14 hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 72 ∗ ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗
     memRegion (s0.sp - 2400#64 + 80#64) 48 ∗ ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗
     memRegion (s0.sp - 2400#64 + 136#64) 8 ∗ ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗
     ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗ memRegion (s0.sp - 2400#64 + 160#64) 2144) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_6904_entails_2304 (s0.sp - 2400#64) esPtr esCap hdrPtr hdrCap))

/-- From `+8588` (`drop_uc_8588`) through `+7084` (`err_7084`) to `s0.x30`
    producing `.error (.err .stateDecode)`. -/
theorem v9_tail_8588_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
        memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  have hdealloc := v9_ct1SentHeap_entails_dealloc A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
    stackAt fsp encoderFromPbStack ∗
    (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
     ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
     ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗ A.pool ∗
     memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 80#64) 48 ∗
     memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 2080 ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))
    (sepConj_mono hdealloc (sepConj_mono_left (v9_stackAt_encoderFromPbStack_to_allocHook fsp)))) ?_
  rw [sepConj_assoc]; apply SepWP.pure_elim; intro _hrk_lt
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
    ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
    ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
    vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗ vecCapPtrDealloc A hdrCap hdrPtr ∗
    vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr ∗ A.pool ∗ stackAt fsp allocHookStack ∗
    (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
     memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
     memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
  refine v9_seq_err_7084 s0 s fsp out pbA _ .stateDecode hsp0_align hfsp_eq
    (SepWP.strengthen_entails_const ?_
      (v9_states_from_pb_drop_uc_8588 hA s0 s fsp out rkPtr rkCap mkPtr mkCap hdrPtr hdrCap esPtr esCap ct1Ptr ct1Cap
        (memRegion (fsp - 5152#64) 1056 ∗ memRegion fsp 48 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 80#64) 48 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
         memRegion (fsp + 224#64) 2080 ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
        hfsp_align hpc hrun hsp hx19 hx28 htr))
    (fun sm ⟨hspm, hx19m, hx28m, htrm⟩ => ⟨hspm, hx19m, by rw [hx28m]; rfl, htrm⟩)
  subst hfsp_eq
  refine Entails.trans (Entails.of_eq (show _ =
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion (s0.sp - 2400#64 - 5152#64) 1056) ∗
    (memRegion (s0.sp - 2400#64) 48 ∗ ((s0.sp - 2400#64 + 48#64) ↦₆₄ ct1Cap) ∗
     ((s0.sp - 2400#64 + 56#64) ↦₆₄ rkCap) ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     ((s0.sp - 2400#64 + 72#64) ↦₆₄ esPtr) ∗ memRegion (s0.sp - 2400#64 + 80#64) 48 ∗
     ((s0.sp - 2400#64 + 128#64) ↦₆₄ esCap) ∗ ((s0.sp - 2400#64 + 136#64) ↦₆₄ mkPtr) ∗
     ((s0.sp - 2400#64 + 144#64) ↦₆₄ hdrPtr) ∗ ((s0.sp - 2400#64 + 152#64) ↦₆₄ hdrCap) ∗
     memRegion (s0.sp - 2400#64 + 160#64) 40 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ct1Ptr) ∗
     memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ mkCap) ∗
     memRegion (s0.sp - 2400#64 + 224#64) 2080) ∗
    statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
    (memRegion pbA optProtoInnerStateSize ∗ A.pool) by ac_rfl)) ?_
  exact sepConj_mono (v9_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64))
    (sepConj_mono_left (v9_fsp_8588_entails_2304 (s0.sp - 2400#64)
      ct1Cap rkCap esPtr esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap))

/-- From `+3044` (after `decoderFromPb` returns) to `s0.x30`. -/
theorem v9_tail_3044_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (d : PolynomialDecoder)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_eq : fsp = s0.sp - 2400#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3044#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) (hx21 : s.readReg64 .x21 = fsp + 848#64)
    (hx24 : s.readReg64 .x24 = fsp + 1888#64) (hx25 : s.readReg64 .x25 = esLen)
    (hx26 : s.readReg64 .x26 = rkLen) (hx28 : s.readReg64 .x28 = rkPtr) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (resultPolyDecoderFromPbAt A (fsp + 1888#64) (decoderFromPbResult (pbToProtoPolyDecoder d)) ∗
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
        ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7
          (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 8 ∗
        memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
        memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
        v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
          esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
        memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (match decoderFromPbResult (pbToProtoPolyDecoder d) with
             | .ok dec => .ok (.ct1Acknowledged { uc := uc, receiving_ek := (dec : spqrPolyApi.PolyDecoder) })
             | .error _ => .error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := hfsp_eq ▸ sp_sub_2400_align s0.sp hsp0_align
  cases decoderFromPbResult (pbToProtoPolyDecoder d) with
  | error err =>
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8588#64)
      (v9_step_3044_err_to_8588 s0 s fsp out rkPtr err _
        hfsp_align hpc hrun hsp hx19 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx28_1, htr1⟩
    refine SepWP.weaken_pre ?_
      (v9_tail_8588_to_ret hA s0 s1 fsp out pbA
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc
        hsp0_align hfsp_eq hpc1 hrun1 hsp1 hx19_1 hx28_1 htr1)
    refine Entails.trans (Entails.of_eq (show _ =
      ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen)) ∗
       (((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 8 ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 28) ∗
       (memRegion (fsp + 224#64) 16 ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 641 ∗ memRegion (fsp + 896#64) 40 ∗
        memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 1888#64) 400 ∗ memRegion (fsp + 2288#64) 16)) ∗
      (((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
       ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
       ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
       memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 160#64) 40 ∗ memRegion (fsp + 208#64) 8 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (v9_memRegion_3044_collapse_err fsp mkLen hdrLen
      (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch
      ((EncoderFromPb.loByte ct1Len).zeroExtend 32))) (Entails.of_eq (by ac_rfl))
  | ok dec =>
    dsimp only [resultPolyDecoderFromPbAt]
    refine SepWP.weaken_pre (Entails.trans
      (sepConj_mono_left (v9_polyDecoderAt_relocate A (fsp + 1888#64) (out + 136#64) dec))
      (Entails.of_eq (show _ =
        (∃∗ bs : { l : List (BitVec 8) // l.length = 384 }, ∃∗ w392 : BitVec 64, ∃∗ P_heap : SepProp,
          ⌜(v9_wordAt bs.val 0).toNat < 2 ^ 63 ∧ EncoderFromPb.loByte w392 = boolByte dec.isComplete ∧
            (((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
             (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec)⌝ ∗
          ((fsp + 1888#64) ↦ₛ bs.val) ∗ (((fsp + 1888#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((fsp + 1888#64) + 392#64) ↦₆₄ w392) ∗ P_heap) ∗
        (memRegion (fsp + 88#64) 8 ∗ memRegion (fsp + 100#64) 28 ∗ memRegion (fsp + 160#64) 40 ∗
         memRegion (fsp + 208#64) 8 ∗ memRegion (fsp + 224#64) 16 ∗ memRegion (fsp + 255#64) 641) ∗
        (((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
         ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
         ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
         ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
         ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗
         memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl))) ?_
    refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (v9_memRegion_3044_split_ok fsp))) ?_
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine ProofLib.SepWP.exists_left fun w888 => ProofLib.SepWP.exists_left fun w880 =>
      ProofLib.SepWP.exists_left fun w864 => ProofLib.SepWP.exists_left fun q848 =>
      ProofLib.SepWP.exists_left fun w832 => ProofLib.SepWP.exists_left fun q816 =>
      ProofLib.SepWP.exists_left fun q800 => ProofLib.SepWP.exists_left fun q784 =>
      ProofLib.SepWP.exists_left fun q768 => ProofLib.SepWP.exists_left fun q752 =>
      ProofLib.SepWP.exists_left fun q736 => ProofLib.SepWP.exists_left fun q720 =>
      ProofLib.SepWP.exists_left fun q704 => ProofLib.SepWP.exists_left fun q688 =>
      ProofLib.SepWP.exists_left fun q672 => ProofLib.SepWP.exists_left fun q656 =>
      ProofLib.SepWP.exists_left fun q640 => ProofLib.SepWP.exists_left fun q624 =>
      ProofLib.SepWP.exists_left fun q608 => ProofLib.SepWP.exists_left fun w592 =>
      ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w232 =>
      ProofLib.SepWP.exists_left fun w224 => ProofLib.SepWP.exists_left fun w208 =>
      ProofLib.SepWP.exists_left fun w192 => ProofLib.SepWP.exists_left fun d172 =>
      ProofLib.SepWP.exists_left fun w160 => ProofLib.SepWP.exists_left fun w120 =>
      ProofLib.SepWP.exists_left fun w112 => ProofLib.SepWP.exists_left fun w104 =>
      ProofLib.SepWP.exists_left fun d92 => ProofLib.SepWP.exists_left fun bs =>
      ProofLib.SepWP.exists_left fun w392 => ProofLib.SepWP.exists_left fun P_heap => ?_
    apply SepWP.pure_elim; rintro ⟨hw0_lt, _, hreloc⟩
    wp_conv_pre => rw [v9_bs384_eq_decCells bs.val bs.property (fsp + 1888#64)]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
      ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
      ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
      ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
      ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗ ((fsp + 144#64) ↦₆₄ hdrPtr) ∗
      ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗ ((fsp + 172#64) ↦₃₂ d172) ∗
      ((fsp + 192#64) ↦₆₄ w192) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ w208) ∗
      ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 232#64) ↦₆₄ w232) ∗
      ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
      ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
      ((fsp + 608#64) ↦₁₂₈ q608) ∗ ((fsp + 624#64) ↦₁₂₈ q624) ∗ ((fsp + 640#64) ↦₁₂₈ q640) ∗
      ((fsp + 656#64) ↦₁₂₈ q656) ∗ ((fsp + 672#64) ↦₁₂₈ q672) ∗ ((fsp + 688#64) ↦₁₂₈ q688) ∗
      ((fsp + 704#64) ↦₁₂₈ q704) ∗ ((fsp + 720#64) ↦₁₂₈ q720) ∗ ((fsp + 736#64) ↦₁₂₈ q736) ∗
      ((fsp + 752#64) ↦₁₂₈ q752) ∗ ((fsp + 768#64) ↦₁₂₈ q768) ∗ ((fsp + 784#64) ↦₁₂₈ q784) ∗
      ((fsp + 800#64) ↦₁₂₈ q800) ∗ ((fsp + 816#64) ↦₁₂₈ q816) ∗ ((fsp + 832#64) ↦₆₄ w832) ∗
      ((fsp + 848#64) ↦₁₂₈ q848) ∗ ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
      ((fsp + 880#64) ↦₆₄ w880) ∗ ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
      v9_decCellsAt (fsp + 1888#64) bs.val ∗
      ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 2280#64) ↦₆₄ w392) ∗
      (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
       memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
       memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
       memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
       memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
       v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
    refine EncoderFromPb.seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
      (v9_step_3044_ok_to_8180 s0 s fsp out
        rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc.epoch
        w104 w112 w120 w160 w192 w208 w224 w232 w832 w864 w880 w888 (BitVec.ofNat 64 dec.ptsNeeded) w392 d172
        q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848 bs.val _
        hfsp_align hw0_lt hpc hrun hsp hx19 hx21 hx24 hx25 hx26 hx28 htr) ?_
    intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1,
      hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx18_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx27_32_1,
      hx28_1, hx30_1, htr1⟩
    have hpre8180 :
        ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗ ((fsp + 56#64) ↦₆₄ rkCap) ∗
        ((fsp + 72#64) ↦₆₄ esPtr) ∗ ((fsp + 80#64) ↦₆₄ hdrLen) ∗
        ((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗
        ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗ ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 120#64) ↦₆₄ w392) ∗ ((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
        ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap) ∗ ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
        ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
        ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
        ((fsp + 216#64) ↦₆₄ mkCap) ∗ ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗
        ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
        ((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
        ((fsp + 247#64) ↦₆₄ uc.epoch) ∗
        ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
        ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
        ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
        ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
        ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
        ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
        ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
        ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
        ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
        ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
        ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
        ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
        v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
        ((fsp + 2280#64) ↦₆₄ w392) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         memRegion fsp 40 ∗ memRegion (fsp + 64#64) 8 ∗ memRegion (fsp + 88#64) 4 ∗ memRegion (fsp + 100#64) 4 ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 255#64) 313 ∗
         memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗
         memRegion (fsp + 871#64) 9 ∗ memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗
         memRegion (fsp + 936#64) 952 ∗ memRegion (fsp + 2288#64) 16 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) ⊢
        (∃∗ bs240 : { l : List (BitVec 8) // l.length = 328 }, ((fsp + 240#64) ↦ₛ bs240.val)) ∗
        (((fsp + 1888#64) ↦₁₂₈ (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)) ∗
         ((fsp + 1904#64) ↦₁₂₈ (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16)) ∗
         ((fsp + 1920#64) ↦₆₄ v9_wordAt bs.val 32) ∗ memRegion (fsp + 1928#64) 376) ∗
        (memRegion fsp 92 ∗ memRegion (fsp + 96#64) 8 ∗ memRegion (fsp + 128#64) 32 ∗
         memRegion (fsp + 200#64) 8 ∗ memRegion (fsp + 216#64) 8 ∗ memRegion (fsp + 895#64) 993) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) := by
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 240#64) ↦ₛ EncoderFromPb.loBytes7 (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))) ∗
         ((fsp + 247#64) ↦₆₄ uc.epoch) ∗ memRegion (fsp + 255#64) 313) ∗
        (v9_decCellsAt (fsp + 1888#64) bs.val ∗ ((fsp + 2272#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
         ((fsp + 2280#64) ↦₆₄ w392) ∗ memRegion (fsp + 2288#64) 16) ∗
        ((memRegion fsp 40 ∗ ((fsp + 40#64) ↦₆₄ mkLen) ∗ ((fsp + 48#64) ↦₆₄ ct1Cap) ∗
          ((fsp + 56#64) ↦₆₄ rkCap) ∗ memRegion (fsp + 64#64) 8 ∗ ((fsp + 72#64) ↦₆₄ esPtr) ∗
          ((fsp + 80#64) ↦₆₄ hdrLen) ∗ memRegion (fsp + 88#64) 4) ∗
         (((fsp + 96#64) ↦₃₂ (EncoderFromPb.loByte ct1Len).zeroExtend 32) ∗ memRegion (fsp + 100#64) 4) ∗
         (((fsp + 128#64) ↦₆₄ esCap) ∗ ((fsp + 136#64) ↦₆₄ mkPtr) ∗
          ((fsp + 144#64) ↦₆₄ hdrPtr) ∗ ((fsp + 152#64) ↦₆₄ hdrCap)) ∗
         ((fsp + 200#64) ↦₆₄ ct1Ptr) ∗ ((fsp + 216#64) ↦₆₄ mkCap) ∗
         (memRegion (fsp + 895#64) 1 ∗ memRegion (fsp + 896#64) 40 ∗ memRegion (fsp + 936#64) 952)) ∗
        (((fsp + 92#64) ↦₃₂ d92) ∗ ((fsp + 104#64) ↦₆₄ v9_wordAt bs.val 376) ∗
         ((fsp + 112#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗ ((fsp + 120#64) ↦₆₄ w392) ∗
         ((fsp + 160#64) ↦₆₄ v9_wordAt bs.val 312) ∗
         ((fsp + 172#64) ↦₃₂ (EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32) ∗
         ((fsp + 192#64) ↦₆₄ v9_wordAt bs.val 360) ∗ ((fsp + 208#64) ↦₆₄ rkPtr) ∗
         ((fsp + 224#64) ↦₆₄ v9_wordAt bs.val 344) ∗ ((fsp + 232#64) ↦₆₄ v9_wordAt bs.val 296) ∗
         ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
         ((fsp + 608#64) ↦₁₂₈ v9_quadAt bs.val 32) ∗ ((fsp + 624#64) ↦₁₂₈ v9_quadAt bs.val 48) ∗
         ((fsp + 640#64) ↦₁₂₈ v9_quadAt bs.val 64) ∗ ((fsp + 656#64) ↦₁₂₈ v9_quadAt bs.val 80) ∗
         ((fsp + 672#64) ↦₁₂₈ v9_quadAt bs.val 96) ∗ ((fsp + 688#64) ↦₁₂₈ v9_quadAt bs.val 112) ∗
         ((fsp + 704#64) ↦₁₂₈ v9_quadAt bs.val 128) ∗ ((fsp + 720#64) ↦₁₂₈ v9_quadAt bs.val 144) ∗
         ((fsp + 736#64) ↦₁₂₈ v9_quadAt bs.val 160) ∗ ((fsp + 752#64) ↦₁₂₈ v9_quadAt bs.val 176) ∗
         ((fsp + 768#64) ↦₁₂₈ v9_quadAt bs.val 192) ∗ ((fsp + 784#64) ↦₁₂₈ v9_quadAt bs.val 208) ∗
         ((fsp + 800#64) ↦₁₂₈ v9_quadAt bs.val 224) ∗ ((fsp + 816#64) ↦₁₂₈ v9_quadAt bs.val 240) ∗
         ((fsp + 832#64) ↦₆₄ v9_wordAt bs.val 256) ∗
         ((fsp + 848#64) ↦₁₂₈ v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24)) ∗
         ((fsp + 864#64) ↦ₛ EncoderFromPb.loBytes7 (v9_wordAt bs.val 24 >>> 8)) ∗
         ((fsp + 880#64) ↦₆₄ EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) ∗
         ((fsp + 888#64) ↦ₛ EncoderFromPb.loBytes7 (uc.epoch >>> 8)) ∗
         memRegion (fsp + 168#64) 4 ∗ memRegion (fsp + 176#64) 16 ∗ memRegion (fsp + 568#64) 8 ∗
         memRegion (fsp + 599#64) 9 ∗ memRegion (fsp + 840#64) 8 ∗ memRegion (fsp + 871#64) 9 ∗
         v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
         P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool ∗ stackAt fsp encoderFromPbStack ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize) by ac_rfl)) ?_
      exact sepConj_mono (v9_loBytes7_64_313_entails_bs328 fsp
        (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch)) uc.epoch)
        (sepConj_mono (v9_fsp_1888_entails_epilogue fsp (BitVec.ofNat 64 dec.ptsNeeded) w392 bs.val bs.property)
          (sepConj_mono_left (v9_fsp_8180_gaps_collapse fsp mkLen ct1Cap rkCap esPtr hdrLen
            esCap mkPtr hdrPtr hdrCap ct1Ptr mkCap ((EncoderFromPb.loByte ct1Len).zeroExtend 32))))
    refine SepWP.weaken_pre hpre8180 ?_
    subst hfsp_eq; rw [sepExists_sepConj_left]
    apply ProofLib.SepWP.exists_left; intro bs240
    have hep := states_from_pb_epilogue_8180 hA s0 s1 out
      d92 ((EncoderFromPb.loByte (v9_wordAt bs.val 8)).zeroExtend 32)
      (v9_wordAt bs.val 376) (BitVec.ofNat 64 dec.ptsNeeded) w392
      (v9_wordAt bs.val 312) (v9_wordAt bs.val 360) rkPtr
      (v9_wordAt bs.val 344) (v9_wordAt bs.val 296) bs240.val bs240.property q576 w592
      (v9_quadAt bs.val 32) (v9_quadAt bs.val 48) (v9_quadAt bs.val 64) (v9_quadAt bs.val 80)
      (v9_quadAt bs.val 96) (v9_quadAt bs.val 112) (v9_quadAt bs.val 128) (v9_quadAt bs.val 144)
      (v9_quadAt bs.val 160) (v9_quadAt bs.val 176) (v9_quadAt bs.val 192) (v9_quadAt bs.val 208)
      (v9_quadAt bs.val 224) (v9_quadAt bs.val 240) (v9_wordAt bs.val 256)
      (v9_midQ128 (v9_wordAt bs.val 8) (v9_wordAt bs.val 16) (v9_wordAt bs.val 24))
      (v9_wordAt bs.val 24 >>> 8) (EncoderFromPb.unshiftWord ct1Len (EncoderFromPb.loByte uc.epoch))
      (uc.epoch >>> 8) (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
      (v9_ct1SentHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
         esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc ∗
       P_heap ∗ memRegion pbA optProtoInnerStateSize ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp1 hx6_1 hx19_1 hx23_1 htr1
    rw [hx8_1, hx15_1, hx20_1, hx13_1, hx25_1, hx30_1, hx9_1, hx14_1, hx18_1, hx17_1, hx0_1,
        hx3_1, hx27_32_1, hx27_1, hx4_1, hx5_1, hx21_1, hx7_1, hx2_1, hx11_1, hx22_1, hx24_1,
        hx10_1, hx26_1, hx12_1, hx1_1, hx28_1, hx16_1] at hep
    refine SepWP.weaken_pre (by unfold epilogueStackSlots epilogueStackGaps; exact Entails.of_eq (by ac_rfl))
      (SepWP.mono hep fun sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩ => ⟨Entails.trans hPf ?_, hsp_f, hcc_f, htr_f⟩)
    have hb96 : (esLen.extractLsb' 0 32).setWidth 8 = esLen.extractLsb' 0 8 := by bv_kernel
    have hd97 : (esLen >>> 8).extractLsb' 0 32 = esLen.extractLsb' 8 32 := by bv_kernel
    have hh101 : (((esLen >>> 8) >>> 32).setWidth 32).setWidth 16 = esLen.extractLsb' 40 16 := by bv_kernel
    have hb103 : (((esLen >>> 8) >>> 48).setWidth 32).setWidth 8 = esLen.extractLsb' 56 8 := by bv_kernel
    have hb120 : ((EncoderFromPb.loByte ct1Len).zeroExtend 32).setWidth 8 = EncoderFromPb.loByte ct1Len :=
      v9_zext32_setWidth8 (EncoderFromPb.loByte ct1Len)
    rw [hb96, hd97, hh101, hb103, hb120]
    have hreloc' :
        ((out + 136#64) ↦ₛ bs.val) ∗ (((out + 136#64) + 384#64) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
          (((out + 136#64) + 392#64) ↦₆₄ w392) ∗ P_heap ⊢ polyDecoderAt A (out + 136#64) dec := by
      simpa only [v9_bv_add_add_lit, Nat.reduceAdd] using hreloc
    have hout := v9_epilogueOutFull_entails_ct1Acknowledged A (F := F) out
      rkCap rkPtr rkLen mkCap mkPtr mkLen hdrCap hdrPtr hdrLen
      esCap esPtr esLen ct1Cap ct1Ptr ct1Len uc bs.val bs.property w392 dec P_heap hreloc'
      (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592) bs240.val bs240.property
      (v9_wordAt bs.val 8 ++ v9_wordAt bs.val 0)
      (v9_wordAt bs.val 24 ++ v9_wordAt bs.val 16) (v9_wordAt bs.val 32)
    exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hout)

end CryptoVerification.SpqrV1.States.FromPb
