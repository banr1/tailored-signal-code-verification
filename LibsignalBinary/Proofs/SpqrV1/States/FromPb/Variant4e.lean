/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4b
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4d
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 4 (`EkSentCt1Received`, `+248`)

Top-level composition and `subroutine_ok` contract for `InnerState.ekSentCt1Received`.
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

/-! ## Stack & Heap Helpers (`v4e_*`) -/

theorem v4e_optProtoPolyDecoderHeap_some_info (A : RustAlloc) (pb : ProtoPolynomialDecoder)
    (d0 d8 d16 : BitVec 64) (d24 d28 : BitVec 32) (d32 : BitVec 64) :
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 ⊢
    ⌜d0.toNat < 2 ^ 63 ∧ d24 = pb.ptsNeeded⌝ ∗
    v4b_optProtoPolyDecoderHeap A (some pb) d0 d8 d16 d24 d28 d32 := by
  unfold v4b_optProtoPolyDecoderHeap
  apply Entails.pure_left; rintro ⟨h1, h2, h3, hle, hcap, h6, h7⟩
  have hd0 : d0.toNat < 2 ^ 63 := by omega
  exact Entails.pure_right ⟨hd0, h2⟩ (Entails.pure_right ⟨h1, h2, h3, hle, hcap, h6, h7⟩ (Entails.refl _))

theorem v4e_optProtoUcHeap_none_info (A : RustAlloc)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcHeap A none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ⊢
    ⌜u0 = noneCap⌝ ∗ emp := by
  dsimp only [v4b_optProtoUcHeap]
  exact Entails.of_eq (sepConj_emp _).symm

theorem v4e_ucWordsAt_pbA_eq (pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64) :
    v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 =
      ((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
      (((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
       ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
       ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
       ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80)) := by
  unfold v4b_optProtoUcWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## `+2228 -> +18368 -> +2308 -> ret` when `s.uc = some u` -/

/-- From `+2228`, when `s.uc = some u`:
    steps `+2228 -> +18368`, calls `ekSentCt1ReceivedFromPb`, and dispatches at `+2308` to return. -/
theorem v4e_ekSent_uc_some_2228_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s0 s2 : State) (out pbA d0 d8 d16 d32 : BitVec 64) (d24 d28 : BitVec 32)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 : BitVec 64)
    (u : V1State.Unchunked.EkSentCt1Received)
    (optDecPb : Option PolynomialDecoder) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2228#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 2400#64)
    (hx0_2 : s2.readReg64 .x0 = u56)
    (hx1_2 : s2.readReg64 .x1 = u48)
    (hx8_2 : s2.readReg64 .x8 = u16)
    (hx9_2 : s2.readReg64 .x9 = u40)
    (hx10_2 : s2.readReg64 .x10 = u64)
    (hx11_2 : s2.readReg64 .x11 = u8)
    (hx12_2 : s2.readReg64 .x12 = u32)
    (hx13_2 : s2.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64)
    (hx14_2 : s2.readReg64 .x14 = d28.zeroExtend 64)
    (hx15_2 : s2.readReg64 .x15 = d32)
    (hx19_2 : s2.readReg64 .x19 = out)
    (hx20_2 : s2.readReg64 .x20 = d16)
    (hx21_2 : s2.readReg64 .x21 = u24)
    (hx22_2 : s2.readReg64 .x22 = u0)
    (hx23_2 : s2.readReg64 .x23 = d24.zeroExtend 64)
    (hx24_2 : s2.readReg64 .x24 = d8)
    (hx25_2 : s2.readReg64 .x25 = u80)
    (hx26_2 : s2.readReg64 .x26 = u72)
    (hx27_2 : s2.readReg64 .x27 = pbA)
    (hx28_2 : s2.readReg64 .x28 = d0)
    (htr2 : TraceCalleeSaved s2 s0)
    (hd0_none : optDecPb = none → d0 = noneCap) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s2
      (v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        (pbA ↦₆₄ 0x8000000000000004#64) ∗
        v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
        v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
        memRegion (pbA + 152#64) 72 ∗
        v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        A.pool ∗
        statesFromPbJumpTableAt b)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (match Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
             | .error e => .error e
             | .ok uc =>
               match optDecPb with
               | none => .error (.err .stateDecode)
               | some d =>
                 match decoderFromPbResult (pbToProtoPolyDecoder d) with
                 | .error _ => .error (.err .stateDecode)
                 | .ok dec => .ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  let fsp := s0.sp - 2400#64
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := v4d_fsp_aligned s0.sp hsp0_align
  refine SepWPp.weaken_pre
    (Entails.trans
      (sepConj_mono_left (v4d_optProtoUcHeap_some_u0_lt A u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96))
      (Entails.of_eq (sepConj_assoc _ _ _))) ?_
  apply v4d_sepWPp_pure_left; intro hu0_lt
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (sepConj_left_comm _ _ _))
      (sepConj_mono_left (v4d_memRegion_2304_split_2228 fsp))) ?_
  apply v4d_sepWPp_exists_left; intro v224; apply v4d_sepWPp_exists_left; intro v232
  apply v4d_sepWPp_exists_left; intro s0_u; apply v4d_sepWPp_exists_left; intro s8_u
  apply v4d_sepWPp_exists_left; intro s16_u; apply v4d_sepWPp_exists_left; intro s24_u
  apply v4d_sepWPp_exists_left; intro s32_u; apply v4d_sepWPp_exists_left; intro s40_u
  apply v4d_sepWPp_exists_left; intro s48_u; apply v4d_sepWPp_exists_left; intro s56_u
  apply v4d_sepWPp_exists_left; intro s64_u; apply v4d_sepWPp_exists_left; intro s72_u
  apply v4d_sepWPp_exists_left; intro s80_u; apply v4d_sepWPp_exists_left; intro s88_u
  apply v4d_sepWPp_exists_left; intro s96_u
  have h18368 := v4b_step_2228_some_to_18368 (b := b) (ext := ext)
    s2 fsp pbA out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
    s0_u s8_u s16_u s24_u s32_u s40_u s48_u s56_u s64_u s72_u s80_u s88_u s96_u
    v224 v232 d0 d8 d16 d24 d28 d32
    ((((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
      ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
      ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
      ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80)) ∗
     (pbA ↦₆₄ 0x8000000000000004#64) ∗
     v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
     memRegion (pbA + 152#64) 72 ∗
     memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
     memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1888#64) 104 ∗
     memRegion (fsp + 1992#64) 312 ∗
     v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
     v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
     stackAt fsp encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ A.pool ∗ statesFromPbJumpTableAt b)
    hfsp_align hu0_lt hpc2 hrun2 hsp2
    hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
  refine v4d_seq_clean_p_weaken h18368 ?_ ?_
  · dsimp only [fsp]
    rw [v4e_ucWordsAt_pbA_eq pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96]
    exact Entails.of_eq (by ac_rfl)
  intro sm hpcm hrunm ⟨hsp_m, hx0_m, hx1_m, hx19_m, hx20_m, _, _, hx23_m, hx24_m, _, _, _, hx28_m, hx30_m, htr_m⟩
  have htr_m := htr_m.trans htr2
  have hsp_align_m : sm.spAligned = true := by
    simp only [State.spAligned, hsp_m]; exact hfsp_align
  have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 d24 d28 d32
  have hpack_uc := v4b_protoUcAt_pack A (fsp + 1392#64) u u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
  have hst_ek := v4b_stackAt_encoderFromPbStack_to_ekSent fsp
  refine SepWPp.weaken_pre ?_
    (v4d_sepWPp_call (v4_sub_ok_ek_sent_ct1_received_from_pb (F := F) hA)
      (x := ⟨fsp + 1888#64, fsp + 1392#64, u⟩)
      (P_step := memRegion (fsp + 1888#64) 104 ∗
        protoUnchunkedEkSentCt1ReceivedAt A (fsp + 1392#64) u ∗
        A.pool ∗ stackAt fsp ekSentCt1ReceivedFromPbStack)
      (F := ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
        memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
        memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1992#64) 312 ∗
        memRegion (fsp - 5152#64) 848 ∗
        v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
        statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
        memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
      hpcm hrunm hsp_align_m hx30_m ?_ ?_ (fun _ _ => rfl) ?_)
  · rw [v4e_ucWordsAt_pbA_eq pbA u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96] at hpb
    refine Entails.trans
      (Entails.of_eq (show _ =
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗
         (((pbA + 96#64) ↦₆₄ u88) ∗ ((pbA + 104#64) ↦₆₄ u96) ∗
          (((pbA + 8#64) ↦₆₄ u0) ∗ ((pbA + 16#64) ↦₆₄ u8) ∗ ((pbA + 24#64) ↦₆₄ u16) ∗
           ((pbA + 32#64) ↦₆₄ u24) ∗ ((pbA + 40#64) ↦₆₄ u32) ∗ ((pbA + 48#64) ↦₆₄ u40) ∗
           ((pbA + 56#64) ↦₆₄ u48) ∗ ((pbA + 64#64) ↦₆₄ u56) ∗ ((pbA + 72#64) ↦₆₄ u64) ∗
           ((pbA + 80#64) ↦₆₄ u72) ∗ ((pbA + 88#64) ↦₆₄ u80))) ∗
         v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
         memRegion (pbA + 152#64) 72) ∗
        (v4b_optProtoUcWordsAt (fsp + 1392#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         v4b_optProtoUcHeap A (some u) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96) ∗
        stackAt fsp encoderFromPbStack ∗
        (memRegion (fsp + 1888#64) 104 ∗ A.pool ∗
         ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
         memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1992#64) 312 ∗
         v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTableAt b) by ac_rfl))
      (Entails.trans
        (sepConj_mono hpb (sepConj_mono hpack_uc (sepConj_mono_left hst_ek)))
        (Entails.of_eq (by ac_rfl)))
  · intro R' hm'
    dsimp only [ekSentCt1ReceivedFromPbSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
  · intro sf
    dsimp only [ekSentCt1ReceivedFromPbSpec, statesFromPbOnPanic]
    exact v4_onPanic_frame_entails htr_m
  · intro s3 hpc3 hrun3 hsp3 hcs3
    rcases hcs3 with ⟨hx19_3, hx20_3, _, _, hx23_3, hx24_3, _, _, _, hx28_3, _, hvregs_3⟩
    rw [hx19_m] at hx19_3; rw [hx20_m] at hx20_3; rw [hx23_m] at hx23_3
    rw [hx24_m] at hx24_3; rw [hx28_m] at hx28_3; rw [hsp_m] at hsp3
    dsimp only [ekSentCt1ReceivedFromPbSpec]
    rw [sepConj_assoc]
    apply v4d_sepWPp_pure_left; intro htr3_m
    have htr3 : TraceCalleeSaved s3 s0 := ⟨htr3_m.trans htr_m.1, hvregs_3.trans htr_m.2⟩
    have h1652 := v4d_memRegion_1156_104_392_entails_1652 fsp
    have hst_back := v4b_stackAt_ekSent_to_encoderFromPbStack fsp
    have hpost_merge :
        (ekSentCt1ReceivedResultAt A (F := F) (fsp + 1888#64)
            (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u) ∗
          memRegion (fsp + 1392#64) 104 ∗ A.pool ∗ stackAt sm.sp ekSentCt1ReceivedFromPbStack) ∗
        (((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
         memRegion fsp 224 ∗ memRegion (fsp + 236#64) 1156 ∗
         memRegion (fsp + 1496#64) 392 ∗ memRegion (fsp + 1992#64) 312 ∗
         memRegion (fsp - 5152#64) 848 ∗
         v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) ⊢
        ekSentCt1ReceivedResultAt A (F := F) (fsp + 1888#64)
            (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u) ∗
          memRegion fsp 224 ∗
          memRegion (fsp + 236#64) 1652 ∗
          ((fsp + 224#64) ↦₆₄ d32) ∗
          ((fsp + 232#64) ↦₃₂ d28) ∗
          memRegion (fsp + 1992#64) 312 ∗
          v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
          stackAt fsp encoderFromPbStack ∗
          statesFromPbSavedCells s0 ∗
          memRegion out chunkedStatesSize ∗
          A.pool ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b := by
      rw [hsp_m]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 236#64) 1156 ∗ memRegion (fsp + 1392#64) 104 ∗
           memRegion (fsp + 1496#64) 392) ∗
          (stackAt fsp ekSentCt1ReceivedFromPbStack ∗ memRegion (fsp - 5152#64) 848) ∗
          (ekSentCt1ReceivedResultAt A (F := F) (fsp + 1888#64)
             (Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u) ∗
           memRegion fsp 224 ∗ ((fsp + 224#64) ↦₆₄ d32) ∗ ((fsp + 232#64) ↦₃₂ d28) ∗
           memRegion (fsp + 1992#64) 312 ∗
           v4b_optProtoPolyDecoderHeap A (optDecPb.map pbToProtoPolyDecoder) d0 d8 d16 d24 d28 d32 ∗
           statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b) by ac_rfl))
        (Entails.trans (sepConj_mono h1652 (sepConj_mono_left hst_back)) (Entails.of_eq (by ac_rfl)))
    refine SepWPp.weaken_pre hpost_merge ?_
    cases hres : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u with
    | error e =>
      have he_eq := v4d_ekSent_from_pb_error_eq F u e hres
      subst he_eq
      apply SepWPp.of_sepWP_ret
      have herr := v4d_ekSent_2308_err_to_ret (A := A) (F := F) hA s0 s3 out pbA
        d0 d8 d16 d32 d24 d28 (optDecPb.map pbToProtoPolyDecoder) (.err .stateDecode)
        hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx24_3 hx28_3 htr3
      refine SepWP.weaken_pre ?_ herr
      dsimp only [fsp]; exact Entails.of_eq (by ac_rfl)
    | ok uc =>
      cases optDecPb with
      | none =>
        have hd0_eq := hd0_none rfl
        rw [hd0_eq] at hx28_3
        apply SepWPp.of_sepWP_ret
        dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
        have hnone := v4d_ekSent_2308_ok_none_to_ret (A := A) (F := F) hA s0 s3 out pbA
          d32 d28 uc hsp0_align hpc3 hrun3 hsp3 hx19_3 hx28_3 htr3
        refine SepWP.weaken_pre ?_ hnone
        dsimp only [fsp]
        refine Entails.trans
          (Entails.of_eq (show _ =
            ⌜d0 = noneCap⌝ ∗
            (ekSentCt1ReceivedResultAt A (F := F) ((s0.sp - 2400#64) + 1888#64) (.ok uc) ∗
             memRegion (s0.sp - 2400#64) 224 ∗
             (((s0.sp - 2400#64) + 224#64) ↦₆₄ d32) ∗
             (((s0.sp - 2400#64) + 232#64) ↦₃₂ d28) ∗
             memRegion ((s0.sp - 2400#64) + 236#64) 1652 ∗
             memRegion ((s0.sp - 2400#64) + 1992#64) 312 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             statesFromPbSavedCells s0 ∗
             memRegion out chunkedStatesSize ∗
             A.pool ∗
             memRegion pbA optProtoInnerStateSize ∗
             statesFromPbJumpTableAt b) by ac_rfl))
          (Entails.pure_left (fun _ => Entails.refl _))
      | some d =>
        dsimp only [Option.map]
        exact v4d_ekSent_2308_ok_some_to_ret (A := A) (F := F) hA hdec s0 s3 out pbA
          d0 d8 d16 d32 d24 d28 uc d R
          hsp0_align hpc3 hrun3 hsp3 hx19_3 hx20_3 hx23_3 hx24_3 hx28_3 htr3

/-! ## Top-Level Variant 4 Theorem at `+248` -/

theorem v4e_sepWPp_exists {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {post Qp : State → SepProp → Prop}
    (h : ∀ x, SepWPp prog target_pc s (P x) post Qp) :
    SepWPp prog target_pc s (∃∗ x, P x) post Qp := by
  intro R' hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hmx⟩
  exact h x R' hmx

/-- Full Variant 4 (`EkSentCt1Received`) execution from `+248` (`0x5a19c`) to `s0.x30`. -/
theorem states_from_pb_ekSentCt1Received_248
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hdec : DecoderFromPbOkExt b A ext)
    (s : V1State.Chunked.EkSentCt1Received) (s0 s1 : State) (out pbA : BitVec 64) (R : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 248#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx13_1 : s1.readReg64 .x13 = (s0.sp - 2400#64) + 1264#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (optProtoInnerStateAt A pbA (some (.ekSentCt1Received s)) ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        memRegion (s0.sp - 2400#64) 2304 ∗
        statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        statesFromPbJumpTableAt b ∗
        A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (States.from_pb spqrPolyApi (spqrAuthApi F) { innerState := some (.ekSentCt1Received s) }) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ statesFromPbOnPanic s0 sf ∗ R)) := by
  rcases s with ⟨optUc, optDec⟩
  rw [v4b_optProtoInnerStateAt_ekSentCt1Received_eq A pbA ⟨optUc, optDec⟩]
  dsimp only
  refine SepWPp.weaken_pre
    (sepConj_mono_left
      (sepConj_mono_right
        (sepConj_mono
          (v4b_optProtoUcAt_unpack A (pbA + 8#64) optUc)
          (sepConj_mono_left
            (v4b_optProtoPolyDecoderAt_unpack A (pbA + 112#64) (optDec.map pbToProtoPolyDecoder)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply v4e_sepWPp_exists; intro d0; apply v4e_sepWPp_exists; intro d8
  apply v4e_sepWPp_exists; intro d16; apply v4e_sepWPp_exists; intro d24
  apply v4e_sepWPp_exists; intro d28; apply v4e_sepWPp_exists; intro d32
  apply v4e_sepWPp_exists; intro u0; apply v4e_sepWPp_exists; intro u8
  apply v4e_sepWPp_exists; intro u16; apply v4e_sepWPp_exists; intro u24
  apply v4e_sepWPp_exists; intro u32; apply v4e_sepWPp_exists; intro u40
  apply v4e_sepWPp_exists; intro u48; apply v4e_sepWPp_exists; intro u56
  apply v4e_sepWPp_exists; intro u64; apply v4e_sepWPp_exists; intro u72
  apply v4e_sepWPp_exists; intro u80; apply v4e_sepWPp_exists; intro u88
  apply v4e_sepWPp_exists; intro u96
  cases optDec with
  | none =>
    dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
    refine SepWPp.weaken_pre
      (Entails.of_eq (show _ =
        ⌜d0 = noneCap⌝ ∗
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗
         v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
         memRegion (pbA + 152#64) 72 ∗
         v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl)) ?_
    apply v4d_sepWPp_pure_left; rintro rfl
    have h248 := v4b_step_248_none_to_2228 (b := b) (ext := ext) s1 pbA
      u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d8 d16 d24 d28 d32
      ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
       v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 2304 ∗
       statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
       statesFromPbJumpTableAt b ∗ A.pool)
      hpc1 hrun1 hx27_1
    refine v4d_seq_clean_p_weaken h248 ?_ ?_
    · exact Entails.of_eq (by ac_rfl)
    intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2,
      hx13_2, hx14_2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2,
      hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    rw [hsp1] at hsp2; rw [hx13_1] at hx13_2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
    cases optUc with
    | none =>
      have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 noneCap d8 d16 d24 d28 d32
      rw [v4b_states_from_pb_ekSentCt1Received_none_uc_none_dec F]
      refine SepWPp.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            v4b_optProtoUcHeap A none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
            ((pbA ↦₆₄ 0x8000000000000004#64) ∗
             v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) noneCap d8 d16 d24 d28 d32 ∗
             memRegion (pbA + 152#64) 72) ∗
            (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
             statesFromPbJumpTableAt b) by ac_rfl))
          (Entails.trans
            (sepConj_mono
              (v4e_optProtoUcHeap_none_info A u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96)
              (sepConj_mono_left hpb))
            (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; ac_rfl)))) ?_
      apply v4d_sepWPp_pure_left; intro hu0_eq
      rw [hu0_eq] at hx22_2
      apply SepWPp.of_sepWP_ret
      have hnone := v4d_ekSent_uc_none_2228_to_ret (A := A) (F := F) hA s0 s2 out pbA
        noneCap d8 d16 d32 d24 d28 none hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx24_2 hx28_2 htr2
      refine SepWP.weaken_pre ?_ hnone
      dsimp only [v4b_optProtoPolyDecoderHeap]
      exact Entails.trans (Entails.pure_right rfl (Entails.refl _)) (Entails.of_eq (by ac_rfl))
    | some u =>
      rw [v4b_states_from_pb_ekSentCt1Received_some_uc_none_dec F u]
      have hsome := v4e_ekSent_uc_some_2228_to_ret (A := A) (F := F) hA hdec s0 s2 out pbA
        noneCap d8 d16 d32 d24 d28 u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u none R
        hsp0_align hpc2 hrun2 hsp2
        hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
        (fun _ => rfl)
      refine SepWPp.weaken_pre ?_ hsome
      dsimp only [Option.map, v4b_optProtoPolyDecoderHeap]
      exact Entails.trans
        (Entails.pure_right rfl (Entails.refl _))
        (Entails.of_eq (by ac_rfl))
  | some d =>
    dsimp only [Option.map]
    by_cases hpts : d.ptsNeeded = 80#32
    · refine SepWPp.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
            ((pbA ↦₆₄ 0x8000000000000004#64) ∗
             v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 d24 d28 d32 ∗
             memRegion (pbA + 152#64) 72 ∗
             v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
             stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
             memRegion (s0.sp - 2400#64) 2304 ∗
             statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
             statesFromPbJumpTableAt b ∗ A.pool) by ac_rfl))
          (Entails.trans
            (sepConj_mono_left (v4e_optProtoPolyDecoderHeap_some_info A (pbToProtoPolyDecoder d) d0 d8 d16 d24 d28 d32))
            (Entails.of_eq (sepConj_assoc _ _ _)))) ?_
      apply v4d_sepWPp_pure_left; rintro ⟨hd0_lt, hd24_eq⟩
      change d24 = d.ptsNeeded at hd24_eq
      have hd24_80 : d24 = 80#32 := hd24_eq.trans hpts
      have h248 := v4b_step_248_some_eq_to_2228 (b := b) (ext := ext) s1 pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 d28 d32
        ((pbA ↦₆₄ 0x8000000000000004#64) ∗ memRegion (pbA + 152#64) 72 ∗
         v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
         v4b_optProtoUcHeap A optUc u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 2304 ∗
         statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
         statesFromPbJumpTableAt b ∗ A.pool)
        hd0_lt hpc1 hrun1 hx27_1
      refine v4d_seq_clean_p_weaken h248 ?_ ?_
      · rw [hd24_80]; exact Entails.of_eq (by ac_rfl)
      intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2,
        hx13_2, hx14_2, hx15_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2,
        hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
      rw [hsp1] at hsp2; rw [hx13_1] at hx13_2; rw [hx19_1] at hx19_2; have htr2 := htr2.trans htr1
      have hx23_2' : s2.readReg64 .x23 = d24.zeroExtend 64 := by
        rw [hx23_2, hd24_80]; rfl
      cases optUc with
      | none =>
        have hpb := v4b_pbA_all_words_entails_memRegion pbA 0x8000000000000004#64
          u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 d0 d8 d16 80#32 d28 d32
        rw [v4b_states_from_pb_ekSentCt1Received_none_uc_some_dec F d hpts]
        refine SepWPp.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              v4b_optProtoUcHeap A none u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
              ((pbA ↦₆₄ 0x8000000000000004#64) ∗
               v4b_optProtoUcWordsAt (pbA + 8#64) u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 ∗
               v4b_optProtoPolyDecoderWordsAt (pbA + 112#64) d0 d8 d16 80#32 d28 d32 ∗
               memRegion (pbA + 152#64) 72) ∗
              (v4b_optProtoPolyDecoderHeap A (some (pbToProtoPolyDecoder d)) d0 d8 d16 d24 d28 d32 ∗
               stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
               memRegion (s0.sp - 2400#64) 2304 ∗
               statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ A.pool ∗
               statesFromPbJumpTableAt b) by ac_rfl))
            (Entails.trans
              (sepConj_mono
                (v4e_optProtoUcHeap_none_info A u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96)
                (sepConj_mono_left hpb))
              (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; ac_rfl)))) ?_
        apply v4d_sepWPp_pure_left; intro hu0_eq
        rw [hu0_eq] at hx22_2
        apply SepWPp.of_sepWP_ret
        have hnone := v4d_ekSent_uc_none_2228_to_ret (A := A) (F := F) hA s0 s2 out pbA
          d0 d8 d16 d32 d24 d28 (some (pbToProtoPolyDecoder d))
          hsp0_align hpc2 hrun2 hsp2 hx19_2 hx20_2 hx22_2 hx24_2 hx28_2 htr2
        exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hnone
      | some u =>
        rw [v4b_states_from_pb_ekSentCt1Received_some_uc_some_dec F u d hpts]
        have hsome := v4e_ekSent_uc_some_2228_to_ret (A := A) (F := F) hA hdec s0 s2 out pbA
          d0 d8 d16 d32 d24 d28 u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u (some d) R
          hsp0_align hpc2 hrun2 hsp2
          hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hx15_2
          hx19_2 hx20_2 hx21_2 hx22_2 hx23_2' hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
          (by intro h; nomatch h)
        refine SepWPp.weaken_pre ?_ hsome
        dsimp only [Option.map]
        rw [← hd24_80]
        exact Entails.of_eq (by ac_rfl)
    · apply SepWPp.of_sepWP_ret
      have herr := v4d_ekSent_err_ptsNeeded_ne_248 (A := A) (F := F) hA s0 s1 out pbA
        u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96
        d0 d8 d16 d24 d28 d32 optUc d hpts hsp0_align hpc1 hrun1 hsp1 hx19_1 hx27_1 htr1
      exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) herr

end CryptoVerification.SpqrV1.States.FromPb
