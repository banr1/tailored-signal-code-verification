/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2d
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsf
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant2hsf` -/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

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
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_memcpy

open CryptoVerification.SpqrV1.Alloc
attribute [local simp, local arm64_norm, local wp_norm]
  v1_w80_d97 v1_w80_h101 v1_w80_b103 v1_zext32_setWidth8
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_bv_add_add_lit
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x25_add_145
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x25_add_145_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_fsp_576_add_15
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_fsp_576_add_15_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x21_add_137
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x21_add_137_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_221
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_221_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_217
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_217_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_141
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_141_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_241
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_241_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_137
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x15_add_137_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x23_add_39
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x23_add_39_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x23_add_15
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_x23_add_15_sext
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_reconstruct_w0
attribute [local simp, local arm64_norm, local wp_norm] v2hsf_orr_x27_w80

namespace Ext4K

/-- Execution segment `+9404 -> +9484`: unpacks `dec` header words from `fsp + 1896..1960` into epilogue
    stack slots and copies `dbs328` (`fsp + 1960..2288`) to `fsp + 240..568` via `memcpy`. -/
theorem v2hsf_step_9404_to_9484
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (fsp out x20_in ca3 epoch : BitVec 64)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328)
    (d92 : BitVec 32) (w104 w112 w120 w192 w592 : BitVec 64) (q576 : BitVec 128) (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = x20_in) (hx21 : s.readReg64 .x21 = fsp + 1392#64)
    (hx22 : s.readReg64 .x22 = fsp + 1888#64) (hx23 : s.readReg64 .x23 = fsp + 848#64)
    (hx25 : s.readReg64 .x25 = fsp + 1792#64) (hx26 : s.readReg64 .x26 = ca3)
    (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9484#64) s
      (stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ d92) ∗
        ((fsp + 104#64) ↦₆₄ w104) ∗ ((fsp + 112#64) ↦₆₄ w112) ∗ ((fsp + 120#64) ↦₆₄ w120) ∗
        ((fsp + 192#64) ↦₆₄ w192) ∗ memRegion (fsp + 240#64) 328 ∗
        ((fsp + 576#64) ↦₁₂₈ q576) ∗ ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 w592) ∗
        ((fsp + 1888#64) ↦₆₄ dw0) ∗ ((fsp + 1896#64) ↦₆₄ dw8) ∗ ((fsp + 1904#64) ↦₆₄ dw16) ∗
        ((fsp + 1912#64) ↦₆₄ dw24) ∗ ((fsp + 1920#64) ↦₆₄ dw32) ∗ ((fsp + 1928#64) ↦₆₄ dw40) ∗
        ((fsp + 1936#64) ↦₆₄ dw48) ∗ ((fsp + 1944#64) ↦₆₄ dw56) ∗ ((fsp + 1952#64) ↦₆₄ dw64) ∗
        ((fsp + 1960#64) ↦ₛ dbs328) ∗ memRegion (fsp + 2288#64) 16 ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt fsp allocHookStack ∗ ((fsp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
          ((fsp + 104#64) ↦₆₄ dw24) ∗ ((fsp + 112#64) ↦₆₄ dw32) ∗ ((fsp + 120#64) ↦₆₄ dw40) ∗
          ((fsp + 192#64) ↦₆₄ dw8) ∗ ((fsp + 240#64) ↦ₛ dbs328) ∗
          ((fsp + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
          ((fsp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (dw64 >>> 8)) ∗
          ((fsp + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((fsp + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
          ((fsp + 1920#64) ↦₆₄ dw32) ∗ memRegion (fsp + 1928#64) 376 ∗ Rest) ∧
        s1.sp = fsp ∧ s1.readReg64 .x19 = out ∧ s1.readReg64 .x20 = dw16 ∧
        s1.readReg64 .x21 = fsp + 1392#64 ∧ s1.readReg64 .x23 = fsp + 848#64 ∧
        s1.readReg64 .x24 = x20_in ∧ s1.readReg64 .x26 = ca3 ∧
        s1.readReg64 .x28 = epoch ∧ TraceCalleeSaved s1 s0) := by
  subst hsp
  have hmemcpy := hA.session_memcpy_ok_at statesFromPbName (num% (ls_rel% "<spqr::v1::chunked::states::States>::from_pb" "memcpy"))
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy ⊢
  rw [← hdbs328]
  states_from_pb_fetches_range b (Rust.withPanics ext) 9404 80
  dsimp only [contractProg, tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_simp_pre [pointsTo128, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_conv_pre => rw [v2hsf_fsp_1936_realign_rest s.sp dw48 dw56 dw64]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre =>
    rw [v2hsf_fsp_1936_unrealign_rest s.sp dw48 dw56 dw64,
        v2hsf_fsp_1936_split_1_7_rest s.sp dw48,
        v2hsf_fsp_584_realign_rest s.sp ((v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) w592]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_call hmemcpy (s.sp + 240#64, s.sp + 1960#64, dbs328)
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [v2hsf_fsp_584_unrealign_midQ128_rest s.sp dw48 dw56 dw64,
        v2hsf_fsp_1936_unsplit_1_7_rest s.sp dw48]
    have hep1888 := v2hsf_fsp_1888_entails_epilogue s.sp
      dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328
    simp only [pointsTo128, stackAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hep1888 ⊢
    refine Entails.trans (Entails.of_eq (show _ =
      (((s.sp + 1888#64) ↦₆₄ dw0) ∗ ((s.sp + 1896#64) ↦₆₄ dw8) ∗ ((s.sp + 1904#64) ↦₆₄ dw16) ∗
       ((s.sp + 1912#64) ↦₆₄ dw24) ∗ ((s.sp + 1920#64) ↦₆₄ dw32) ∗ ((s.sp + 1928#64) ↦₆₄ dw40) ∗
       ((s.sp + 1936#64) ↦₆₄ dw48) ∗ ((s.sp + 1944#64) ↦₆₄ dw56) ∗ ((s.sp + 1952#64) ↦₆₄ dw64) ∗
       ((s.sp + 1960#64) ↦ₛ dbs328) ∗ memRegion (s.sp + 2288#64) 16) ∗
      (memRegion (s.sp - 4096#64) 4096 ∗ ((s.sp + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
       ((s.sp + 104#64) ↦₆₄ dw24) ∗ ((s.sp + 112#64) ↦₆₄ dw32) ∗ ((s.sp + 120#64) ↦₆₄ dw40) ∗
       ((s.sp + 192#64) ↦₆₄ dw8) ∗ ((s.sp + 240#64) ↦ₛ dbs328) ∗
       ((s.sp + 576#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 0 64) ∗
       ((s.sp + 584#64) ↦₆₄ (v1_midQ128 dw48 dw56 dw64).extractLsb' 64 64) ∗
       ((s.sp + 592#64) ↦ₛ EncoderFromPb.loBytes7 (dw64 >>> 8)) ∗ Rest) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hep1888) (Entails.of_eq (by ac_rfl))
  · wp_done

set_option maxHeartbeats 1200000 in
/-- Compose `+9404 -> +9484 -> +8180` with `states_from_pb_epilogue_8180` and
    `v2hsf_epilogueOutFull_entails_headerSent`. -/
theorem v2hsf_headerSent_ok_9404_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s : State) (out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch : BitVec 64)
    (bs : List (BitVec 8)) (hbs : bs.length = 384) (hi32 : BitVec 32) (enc : PolyEncoder) (P_enc_heap : SepProp)
    (henc_reloc : ((out + 8#64) ↦₆₄ tag) ∗ (((out + 8#64) + 8#64) ↦ₛ bs) ∗
      (((out + 8#64) + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_enc_heap ⊢ polyEncoderAt A (out + 8#64) enc)
    (dk rootKey macKey : List (BitVec 8)) (hdk : la3 = BitVec.ofNat 64 dk.length)
    (hl1 : ca1 = BitVec.ofNat 64 rootKey.length) (hl2 : ca2 = BitVec.ofNat 64 macKey.length)
    (dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 : BitVec 64)
    (dbs328 : List (BitVec 8)) (hdbs328 : dbs328.length = 328) (dec : PolyDecoder) (P_dec_heap : SepProp)
    (hdec_reloc : ((out + 488#64) ↦₆₄ dw0) ∗ (((out + 488#64) + 8#64) ↦₆₄ dw8) ∗
      (((out + 488#64) + 16#64) ↦₆₄ dw16) ∗ (((out + 488#64) + 24#64) ↦₆₄ dw24) ∗
      (((out + 488#64) + 32#64) ↦₆₄ dw32) ∗ (((out + 488#64) + 40#64) ↦₆₄ dw40) ∗
      (((out + 488#64) + 48#64) ↦₆₄ dw48) ∗ (((out + 488#64) + 56#64) ↦₆₄ dw56) ∗
      (((out + 488#64) + 64#64) ↦₆₄ dw64) ∗ (((out + 488#64) + 72#64) ↦ₛ dbs328) ∗
      P_dec_heap ⊢ polyDecoderAt A (out + 488#64) dec)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9404#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 2400#64) (hx19 : s.readReg64 .x19 = out)
    (hx20 : s.readReg64 .x20 = (loByte (v1_wordAt bs 0)).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (s0.sp - 2400#64) + 1392#64)
    (hx22 : s.readReg64 .x22 = (s0.sp - 2400#64) + 1888#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 2400#64) + 1792#64)
    (hx26 : s.readReg64 .x26 = ca3) (hx28 : s.readReg64 .x28 = epoch) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion (s0.sp - 2400#64) 56 ∗
        ((s0.sp - 2400#64 + 56#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 2400#64 + 64#64) 32 ∗
        ((s0.sp - 2400#64 + 96#64) ↦₆₄ la3) ∗ memRegion (s0.sp - 2400#64 + 104#64) 72 ∗
        ((s0.sp - 2400#64 + 176#64) ↦₆₄ pa3) ∗ ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗
        memRegion (s0.sp - 2400#64 + 192#64) 8 ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ca1) ∗
        memRegion (s0.sp - 2400#64 + 208#64) 8 ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ dw0) ∗
        memRegion (s0.sp - 2400#64 + 224#64) 8 ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ ca2) ∗
        memRegion (s0.sp - 2400#64 + 240#64) 1032 ∗ ((s0.sp - 2400#64 + 1272#64) ↦₆₄ pa1) ∗
        memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ v1_encCellsAt (s0.sp - 2400#64 + 1392#64) bs ∗
        ((s0.sp - 2400#64 + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
        ((s0.sp - 2400#64 + 1888#64) ↦₆₄ dw0) ∗ ((s0.sp - 2400#64 + 1896#64) ↦₆₄ dw8) ∗
        ((s0.sp - 2400#64 + 1904#64) ↦₆₄ dw16) ∗ ((s0.sp - 2400#64 + 1912#64) ↦₆₄ dw24) ∗
        ((s0.sp - 2400#64 + 1920#64) ↦₆₄ dw32) ∗ ((s0.sp - 2400#64 + 1928#64) ↦₆₄ dw40) ∗
        ((s0.sp - 2400#64 + 1936#64) ↦₆₄ dw48) ∗ ((s0.sp - 2400#64 + 1944#64) ↦₆₄ dw56) ∗
        ((s0.sp - 2400#64 + 1952#64) ↦₆₄ dw64) ∗ ((s0.sp - 2400#64 + 1960#64) ↦ₛ dbs328) ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
        vecU8Payload A ca3 pa3 dk ∗ vecU8Payload A ca1 pa1 rootKey ∗ vecU8Payload A ca2 pa2 macKey ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ resultChunkedStatesAt A (F := F) out
          (.ok (.headerSent
            { uc := { auth := { rootKey := rootKey, macKey := macKey }, dk := dk, epoch := epoch },
              sending_ek := enc, receiving_ct1 := dec })) ∗
          Rest ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true := sp_sub_2400_align s0.sp hsp0_align
  rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (v2hsf_memRegion_64_32_split (s0.sp - 2400#64))
      (sepConj_mono_right (sepConj_mono (v2hsf_memRegion_104_72_split (s0.sp - 2400#64))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono (mem64_entails (s0.sp - 2400#64 + 192#64))
          (sepConj_mono_right (sepConj_mono (mem64_entails (s0.sp - 2400#64 + 208#64))
            (sepConj_mono_right (sepConj_mono (mem64_entails (s0.sp - 2400#64 + 224#64))
              (sepConj_mono_right (sepConj_mono_left
                (v2hsf_memRegion_240_1032_split (s0.sp - 2400#64))))))))))))))))) ?_
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
    ProofLib.SepWP.exists_left fun q576 => ProofLib.SepWP.exists_left fun w224 =>
    ProofLib.SepWP.exists_left fun w208 => ProofLib.SepWP.exists_left fun w192 =>
    ProofLib.SepWP.exists_left fun d172 => ProofLib.SepWP.exists_left fun w160 =>
    ProofLib.SepWP.exists_left fun w120 => ProofLib.SepWP.exists_left fun w112 =>
    ProofLib.SepWP.exists_left fun w104 => ProofLib.SepWP.exists_left fun d92 => ?_
  have h9404 := v2hsf_step_9404_to_9484 hA s0 s (s0.sp - 2400#64) out
    ((loByte (v1_wordAt bs 0)).zeroExtend 64) ca3 epoch
    dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64 dbs328 hdbs328 d92 w104 w112 w120 w192 w592 q576
    (memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 56 ∗
      ((s0.sp - 2400#64 + 56#64) ↦₆₄ tag) ∗ memRegion (s0.sp - 2400#64 + 64#64) 28 ∗
      ((s0.sp - 2400#64 + 96#64) ↦₆₄ la3) ∗ memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      ((s0.sp - 2400#64 + 160#64) ↦₆₄ w160) ∗ memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
      ((s0.sp - 2400#64 + 172#64) ↦₃₂ d172) ∗ ((s0.sp - 2400#64 + 176#64) ↦₆₄ pa3) ∗
      ((s0.sp - 2400#64 + 184#64) ↦₆₄ pa2) ∗ ((s0.sp - 2400#64 + 200#64) ↦₆₄ ca1) ∗
      ((s0.sp - 2400#64 + 208#64) ↦₆₄ w208) ∗ ((s0.sp - 2400#64 + 216#64) ↦₆₄ dw0) ∗
      ((s0.sp - 2400#64 + 224#64) ↦₆₄ w224) ∗ ((s0.sp - 2400#64 + 232#64) ↦₆₄ ca2) ∗
      memRegion (s0.sp - 2400#64 + 568#64) 8 ∗ memRegion (s0.sp - 2400#64 + 599#64) 9 ∗
      ((s0.sp - 2400#64 + 608#64) ↦₁₂₈ q608) ∗ ((s0.sp - 2400#64 + 624#64) ↦₁₂₈ q624) ∗
      ((s0.sp - 2400#64 + 640#64) ↦₁₂₈ q640) ∗ ((s0.sp - 2400#64 + 656#64) ↦₁₂₈ q656) ∗
      ((s0.sp - 2400#64 + 672#64) ↦₁₂₈ q672) ∗ ((s0.sp - 2400#64 + 688#64) ↦₁₂₈ q688) ∗
      ((s0.sp - 2400#64 + 704#64) ↦₁₂₈ q704) ∗ ((s0.sp - 2400#64 + 720#64) ↦₁₂₈ q720) ∗
      ((s0.sp - 2400#64 + 736#64) ↦₁₂₈ q736) ∗ ((s0.sp - 2400#64 + 752#64) ↦₁₂₈ q752) ∗
      ((s0.sp - 2400#64 + 768#64) ↦₁₂₈ q768) ∗ ((s0.sp - 2400#64 + 784#64) ↦₁₂₈ q784) ∗
      ((s0.sp - 2400#64 + 800#64) ↦₁₂₈ q800) ∗ ((s0.sp - 2400#64 + 816#64) ↦₁₂₈ q816) ∗
      ((s0.sp - 2400#64 + 832#64) ↦₆₄ w832) ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      ((s0.sp - 2400#64 + 848#64) ↦₁₂₈ q848) ∗ ((s0.sp - 2400#64 + 864#64) ↦ₛ EncoderFromPb.loBytes7 w864) ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ ((s0.sp - 2400#64 + 880#64) ↦₆₄ w880) ∗
      ((s0.sp - 2400#64 + 888#64) ↦ₛ EncoderFromPb.loBytes7 w888) ∗
      memRegion (s0.sp - 2400#64 + 895#64) 377 ∗ ((s0.sp - 2400#64 + 1272#64) ↦₆₄ pa1) ∗
      memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ v1_encCellsAt (s0.sp - 2400#64 + 1392#64) bs ∗
      ((s0.sp - 2400#64 + 1784#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
      vecU8Payload A ca3 pa3 dk ∗ vecU8Payload A ca1 pa1 rootKey ∗ vecU8Payload A ca2 pa2 macKey ∗ Rest)
    hfsp_align hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx28 htr
  refine SepWP.seq (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) h9404) ?_
  intro s1 P1 hpc1 hrun1 ⟨hP1, hsp1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx26_1, hx28_1, htr1⟩
  have h9484 := v2hsf_step_9484_to_8180 s0 s1 (s0.sp - 2400#64) out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch dw0 dw16
    bs hbs hi32 enc.idx w160 w208 w224 w832 w864 w880 w888 d172
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816 q848
    (stackAt (s0.sp - 2400#64) allocHookStack ∗ ((s0.sp - 2400#64 + 92#64) ↦₃₂ (loByte dw48).zeroExtend 32) ∗
      ((s0.sp - 2400#64 + 104#64) ↦₆₄ dw24) ∗ ((s0.sp - 2400#64 + 112#64) ↦₆₄ dw32) ∗
      ((s0.sp - 2400#64 + 120#64) ↦₆₄ dw40) ∗ ((s0.sp - 2400#64 + 192#64) ↦₆₄ dw8) ∗
      ((s0.sp - 2400#64 + 240#64) ↦ₛ dbs328) ∗ ((s0.sp - 2400#64 + 576#64) ↦₁₂₈ v1_midQ128 dw48 dw56 dw64) ∗
      ((s0.sp - 2400#64 + 592#64) ↦ₛ EncoderFromPb.loBytes7 (dw64 >>> 8)) ∗
      ((s0.sp - 2400#64 + 1888#64) ↦₁₂₈ (dw8 ++ dw0)) ∗ ((s0.sp - 2400#64 + 1904#64) ↦₁₂₈ (dw24 ++ dw16)) ∗
      ((s0.sp - 2400#64 + 1920#64) ↦₆₄ dw32) ∗ memRegion (s0.sp - 2400#64 + 1928#64) 376 ∗
      memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗ memRegion (s0.sp - 2400#64) 56 ∗
      memRegion (s0.sp - 2400#64 + 64#64) 28 ∗ memRegion (s0.sp - 2400#64 + 128#64) 32 ∗
      memRegion (s0.sp - 2400#64 + 168#64) 4 ∗ memRegion (s0.sp - 2400#64 + 568#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 599#64) 9 ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
      memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ memRegion (s0.sp - 2400#64 + 895#64) 377 ∗
      memRegion (s0.sp - 2400#64 + 1280#64) 120 ∗ memRegion (s0.sp - 2400#64 + 1792#64) 96 ∗
      statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗ P_enc_heap ∗ P_dec_heap ∗
      vecU8Payload A ca3 pa3 dk ∗ vecU8Payload A ca1 pa1 rootKey ∗ vecU8Payload A ca2 pa2 macKey ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx26_1 hx28_1 htr1
  refine SepWP.seq (SepWP.weaken_pre (Entails.trans hP1 (Entails.of_eq (by ac_rfl))) h9484) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, hx6_2, hx19_2, hx23_2, hx8_2, hx15_2, hx20_2, hx13_2,
    hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2, hx3_2, hx27_2, hx27_hi16, hx27_hi8,
    hx4_2, hx5_2, hx21_2, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2, hx26_2, hx12_2,
    hx1_2, hx28_2, hx16_2, htr2⟩
  have hgaps := v2hsf_epilogueStackGaps_pack (s0.sp - 2400#64) tag la3 pa3 pa2 ca1 dw0 pa1
  have hP2' : P2 ⊢
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ memRegion out chunkedStatesSize ∗
      epilogueStackSlots (s0.sp - 2400#64) ((loByte dw48).zeroExtend 32)
        ((loByte (v1_wordAt bs 128)).zeroExtend 32) dw24 dw32 dw40 ca2 dw8 (v1_wordAt bs 0) epoch ca2 dbs328
        (v1_midQ128 dw48 dw56 dw64) (dw64 >>> 8)
        (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
        (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
        (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
        (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
        (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) (v1_wordAt bs 144 >>> 8)
        (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8)
        (dw8 ++ dw0) (dw24 ++ dw16) dw32 ∗
      epilogueStackGaps (s0.sp - 2400#64) ∗ statesFromPbSavedCells s0 ∗
      (P_enc_heap ∗ P_dec_heap ∗
       vecU8Payload A ca3 pa3 dk ∗ vecU8Payload A ca1 pa1 rootKey ∗ vecU8Payload A ca2 pa2 macKey ∗ Rest) := by
    refine Entails.trans hP2 ?_
    rw [stackAt_encoderFromPb_split_allocHook (s0.sp - 2400#64)]; unfold epilogueStackSlots
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hgaps))))
    exact Entails.of_eq (by ac_rfl)
  have hep := states_from_pb_epilogue_8180 hA s0 s2 out ((loByte dw48).zeroExtend 32)
    ((loByte (v1_wordAt bs 128)).zeroExtend 32) dw24 dw32 dw40 ca2 dw8 (v1_wordAt bs 0) epoch ca2 dbs328 hdbs328
    (v1_midQ128 dw48 dw56 dw64) (dw64 >>> 8)
    (v1_quadAt bs 152) (v1_quadAt bs 168) (v1_quadAt bs 184) (v1_quadAt bs 200)
    (v1_quadAt bs 216) (v1_quadAt bs 232) (v1_quadAt bs 248) (v1_quadAt bs 264)
    (v1_quadAt bs 280) (v1_quadAt bs 296) (v1_quadAt bs 312) (v1_quadAt bs 328)
    (v1_quadAt bs 344) (v1_quadAt bs 360) (v1_wordAt bs 376)
    (v1_midQ128 (v1_wordAt bs 128) (v1_wordAt bs 136) (v1_wordAt bs 144)) (v1_wordAt bs 144 >>> 8)
    (unshiftWord (v1_wordAt bs 104) (loByte (v1_wordAt bs 112))) (v1_wordAt bs 112 >>> 8)
    (dw8 ++ dw0) (dw24 ++ dw16) dw32
    (P_enc_heap ∗ P_dec_heap ∗
     vecU8Payload A ca3 pa3 dk ∗ vecU8Payload A ca1 pa1 rootKey ∗ vecU8Payload A ca2 pa2 macKey ∗ Rest)
    hsp0_align hpc2 hrun2 hsp2 hx6_2 hx19_2 hx23_2 htr2
  refine SepWP.weaken_pre hP2' (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  rw [hx8_2, hx15_2, hx20_2, hx13_2, hx25_2, hx30_2, hx9_2, hx14_2, hx18_2, hx17_2, hx0_2,
      hx3_2, v1_zext32_setWidth8, hx27_2, hx27_hi16, hx27_hi8, hx4_2, hx5_2,
      hx21_2, v1_zext32_setWidth8, hx7_2, hx2_2, hx11_2, hx22_2, hx24_2, hx10_2,
      hx26_2, hx12_2, hx1_2, hx28_2, hx16_2]
  have hout := v2hsf_epilogueOutFull_entails_headerSent A (F := F)
    out tag ca1 pa1 ca2 pa2 ca3 pa3 la3 epoch bs hbs hi32 enc P_enc_heap henc_reloc
    dk rootKey macKey hdk hl1 hl2 dw0 dw8 dw16 dw24 dw32 dw40 dw48 dw56 dw64
    dbs328 hdbs328 dec P_dec_heap hdec_reloc (dw8 ++ dw0) (dw24 ++ dw16) dw32
  exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left hout)

end Ext4K

end CryptoVerification.SpqrV1.States.FromPb
