/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.EpilogueExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aExt
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-! # `<spqr::v1::chunked::states::States>::from_pb`: 4-KiB Hook Wrapper for `Variant4c` -/

namespace CryptoVerification.SpqrV1.States.FromPb.Ext4K

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.States.FromPb

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

attribute [local irreducible]
  epilogueStackSlots epilogueStackGaps
  v4c_destStackSlots v4c_ucSpillSlots v4c_decWordsAt
  v4c_epilogueSlotsLo v4c_epilogueGapsLo
  v4c_epilogueSlots240 v4c_epilogueGaps240
  v4c_epilogueSlots1888

attribute [local irreducible] v4c_epilogueGapsFixed

theorem v4c_step_8180_ok_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s5 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (dw : v4c_DecWords)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc5 : s5.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 8180#64)
    (hrun5 : s5.status = .Running) (hsp5 : s5.sp = s0.sp - 2400#64)
    (hx0_5 : s5.readReg64 .x0 = ct1Ptr) (hx1_5 : s5.readReg64 .x1 = dw.g4.u360)
    (hx2_5 : s5.readReg64 .x2 = dw.g3.u288)
    (hx3_5 : s5.readReg32 .x3 = ((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32)
    (hx4_5 : s5.readReg64 .x4 = uc.epoch) (hx5_5 : s5.readReg64 .x5 = dw.g0.w0)
    (hx6_5 : s5.readReg64 .x6 = (s0.sp - 2400#64) + 576#64) (hx7_5 : s5.readReg64 .x7 = dw.g0.u24)
    (hx8_5 : s5.readReg64 .x8 = 6#64) (hx9_5 : s5.readReg64 .x9 = dkCap)
    (hx10_5 : s5.readReg64 .x10 = dw.g3.u328) (hx11_5 : s5.readReg64 .x11 = dw.g3.u296)
    (hx12_5 : s5.readReg64 .x12 = dw.g4.u352) (hx13_5 : s5.readReg64 .x13 = mkCap)
    (hx14_5 : s5.readReg64 .x14 = dkPtr) (hx15_5 : s5.readReg64 .x15 = rkCap)
    (hx16_5 : s5.readReg64 .x16 = dw.g4.u392) (hx17_5 : s5.readReg64 .x17 = ct1Cap)
    (hx18_5 : s5.readReg64 .x18 = dkLen) (hx19_5 : s5.readReg64 .x19 = out)
    (hx20_5 : s5.readReg64 .x20 = rkLen)
    (hx21_5 : s5.readReg32 .x21 = (loByte dw.g0.u8).zeroExtend 32)
    (hx22_5 : s5.readReg64 .x22 = dw.g3.u304)
    (hx23_5 : s5.readReg64 .x23 = (s0.sp - 2400#64) + 848#64)
    (hx24_5 : s5.readReg64 .x24 = dw.g3.u312) (hx25_5 : s5.readReg64 .x25 = mkPtr)
    (hx26_5 : s5.readReg64 .x26 = dw.g4.u344) (hx27_5 : s5.readReg64 .x27 = v4c_ct1Len_x27 ct1Len)
    (hx28_5 : s5.readReg64 .x28 = dw.g4.u376) (hx30_5 : s5.readReg64 .x30 = mkLen)
    (htr5 : TraceCalleeSaved s5 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s5
      ((memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
        memRegion (s0.sp - 2400#64 + 88#64) 40 ∗ memRegion (s0.sp - 2400#64 + 152#64) 8 ∗
        v4c_ucSpillSlots (s0.sp - 2400#64) ((ct1Len.extractLsb' 0 8).zeroExtend 64)
          mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
        v4c_destStackSlots (s0.sp - 2400#64)
          dw.g3.u336 ((loByte dw.g0.u32).zeroExtend 32) dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
          dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
          dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
          dw.g3.u280
          (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
          (dw.g0.u48 >>> 8) (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8) ∗
        memRegion (s0.sp - 2400#64 + 168#64) 4 ∗ memRegion (s0.sp - 2400#64 + 176#64) 16 ∗
        memRegion (s0.sp - 2400#64 + 200#64) 8 ∗ memRegion (s0.sp - 2400#64 + 240#64) 368 ∗
        memRegion (s0.sp - 2400#64 + 840#64) 8 ∗ memRegion (s0.sp - 2400#64 + 871#64) 9 ∗
        memRegion (s0.sp - 2400#64 + 895#64) 993 ∗
        v4c_decWordsAt (s0.sp - 2400#64 + 1888#64) dw ∗
        memRegion (s0.sp - 2400#64 + 2288#64) 16) ∗
       (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗ statesFromPbSavedCells s0 ∗
        memRegion out chunkedStatesSize ∗
        (memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         v4c_decHeap A dec dw ∗ statesFromPbJumpTableAt b ∗ A.pool)))
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hstack_8180 := v4c_ok_8180_stack_to_epilogue (s0.sp - 2400#64)
    ((ct1Len.extractLsb' 0 8).zeroExtend 64)
    mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap
    dw.g3.u336 ((loByte dw.g0.u32).zeroExtend 32) dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
    dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
    dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
    dw.g3.u280
    (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
    (dw.g0.u48 >>> 8) (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8) dw
  refine SepWP.weaken_pre (sepConj_mono_left hstack_8180) ?_
  apply v4c_wp_exists_left; intro d92; apply v4c_wp_exists_left; intro w104
  apply v4c_wp_exists_left; intro w112; apply v4c_wp_exists_left; intro w120
  apply v4c_wp_exists_left; intro bs240; apply v4c_wp_exists_left; intro q576
  apply v4c_wp_exists_left; intro w592; apply v4c_wp_exists_left; intro q1888
  apply v4c_wp_exists_left; intro q1904; apply v4c_wp_exists_left; intro w1920
  refine SepWP.weaken_pre (Entails.of_eq (sepConj_assoc _ _ _)) ?_
  have hep := states_from_pb_epilogue_8180 hA s0 s5 out
    d92 ((loByte dw.g0.u32).zeroExtend 32)
    w104 w112 w120 dw.g3.u336 dw.g4.u384 rkPtr dw.g4.u368 dw.g3.u320
    bs240.val bs240.property q576 w592
    dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
    dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
    dw.g3.u280
    (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
    (dw.g0.u48 >>> 8)
    (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
    (dw.g0.w16 >>> 8)
    q1888 q1904 w1920
    (memRegion pbA optProtoInnerStateSize ∗
     v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
     v4c_decHeap A dec dw ∗ statesFromPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc5 hrun5 hsp5 hx6_5 hx19_5 hx23_5 htr5
  have hx27_32_5 : s5.readReg32 .x27 = (v4c_ct1Len_x27 ct1Len).setWidth 32 :=
    congrArg (BitVec.setWidth 32) hx27_5
  rw [hx8_5, hx15_5, hx20_5, hx13_5, hx25_5, hx30_5, hx9_5, hx14_5, hx18_5, hx17_5, hx0_5,
      hx3_5, hx27_32_5, hx27_5, hx4_5, hx5_5, hx21_5, hx7_5, hx2_5, hx11_5, hx22_5, hx24_5,
      hx10_5, hx26_5, hx12_5, hx1_5, hx28_5, hx16_5] at hep
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf ?_, hsp_f, hcs_f, htr_f⟩
  have hok := v4c_epilogueOutFull_entails_ok A F out
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
    uc dec dw w104 w112 w120 d92 q576 w592 bs240.val bs240.property q1888 q1904 w1920
  refine Entails.trans
    (Entails.of_eq (show _ =
      (epilogueOutFull out
        6#64 rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr
        ((((ct1Len.extractLsb' 0 8).zeroExtend 64).setWidth 32).setWidth 8)
        ((v4c_ct1Len_x27 ct1Len).setWidth 32)
        (((v4c_ct1Len_x27 ct1Len >>> 32).setWidth 32).setWidth 16)
        (((v4c_ct1Len_x27 ct1Len >>> 48).setWidth 32).setWidth 8)
        uc.epoch dw.g0.w0 (((loByte dw.g0.u8).zeroExtend 32).setWidth 8)
        (unshiftWord dw.g0.u8 (loByte dw.g0.w16))
        (overlapWord7 (unshiftWord dw.g0.u8 (loByte dw.g0.w16)) (dw.g0.w16 >>> 8))
        dw.g0.u24
        (((loByte dw.g0.u32).zeroExtend 32).setWidth 8)
        (unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40))
        (overlapWord7
          ((unshiftWord dw.g0.u40 (loByte dw.g0.u48) ++ unshiftWord dw.g0.u32 (loByte dw.g0.u40)).extractLsb' 64 64)
          (dw.g0.u48 >>> 8))
        dw.g1.q56 dw.g1.q72 dw.g1.q88 dw.g1.q104 dw.g1.q120 dw.g1.q136 dw.g1.q152
        dw.g2.q168 dw.g2.q184 dw.g2.q200 dw.g2.q216 dw.g2.q232 dw.g2.q248 dw.g2.q264
        dw.g3.u280 dw.g3.u288 dw.g3.u296 dw.g3.u304
        dw.g3.u312 dw.g3.u320 dw.g3.u328 dw.g3.u336
        dw.g4.u344 dw.g4.u352 dw.g4.u360 dw.g4.u368
        dw.g4.u376 dw.g4.u384 dw.g4.u392 w104
        w112 w120 (d92.setWidth 8) q576 (overlapWord7 (q576.extractLsb' 64 64) w592)
        bs240.val q1888 q1904 w1920 ∗
       v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
       v4c_decHeap A dec dw) ∗
      (memRegion pbA optProtoInnerStateSize ∗
       statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl))
    (Entails.trans (sepConj_mono_left hok) (Entails.of_eq (by ac_rfl)))

theorem v4c_step_2472_ok_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s4 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (dw : v4c_DecWords) (d32 : BitVec 64) (d28 : BitVec 32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2472#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out)
    (hx20_4 : s4.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64)
    (hx21_4 : s4.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64)
    (hx22_4 : s4.readReg64 .x22 = dkCap)
    (hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 1888#64)
    (hx24_4 : s4.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64)
    (hx25_4 : s4.readReg64 .x25 = rkLen) (hx26_4 : s4.readReg64 .x26 = rkPtr)
    (hx27_4 : s4.readReg64 .x27 = (s0.sp - 2400#64) + 1792#64) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s4
      (v4c_decHeap A dec dw ∗
       ((memRegion (s0.sp - 2400#64 + 152#64) 64 ∗ ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗
         ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗ memRegion (s0.sp - 2400#64 + 236#64) 1652) ∗
        (v4c_decWordsAt (s0.sp - 2400#64 + 1888#64) dw ∗
         stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
         memRegion (s0.sp - 2400#64 + 88#64) 40 ∗
         v4c_ucSpillSlots (s0.sp - 2400#64) ((ct1Len.extractLsb' 0 8).zeroExtend 64)
           mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
         memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
         v4b_ekSentCt1ReceivedHeap A
           rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
         statesFromPbJumpTableAt b ∗ A.pool)))
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (Entails.trans (sepConj_mono_left (v4c_decHeap_entails_w0_lt A dec dw))
    (Entails.of_eq (sepConj_assoc _ _ _))) ?_
  apply SepWP.pure_elim; intro hw0_lt
  have hsplit_2472 := v4c_ok_2472_stack_split (s0.sp - 2400#64) d32 d28
  refine SepWP.weaken_pre
    (Entails.trans (sepConj_mono_right (sepConj_mono_left hsplit_2472))
      (Entails.of_eq (sepConj_left_comm _ _ _))) ?_
  apply v4c_wp_exists_left; intro w160; apply v4c_wp_exists_left; intro d172
  apply v4c_wp_exists_left; intro w192; apply v4c_wp_exists_left; intro w208
  apply v4c_wp_exists_left; intro w224; apply v4c_wp_exists_left; intro w232
  apply v4c_wp_exists_left; intro q608; apply v4c_wp_exists_left; intro q624
  apply v4c_wp_exists_left; intro q640; apply v4c_wp_exists_left; intro q656
  apply v4c_wp_exists_left; intro q672; apply v4c_wp_exists_left; intro q688
  apply v4c_wp_exists_left; intro q704; apply v4c_wp_exists_left; intro q720
  apply v4c_wp_exists_left; intro q736; apply v4c_wp_exists_left; intro q752
  apply v4c_wp_exists_left; intro q768; apply v4c_wp_exists_left; intro q784
  apply v4c_wp_exists_left; intro q800; apply v4c_wp_exists_left; intro q816
  apply v4c_wp_exists_left; intro w832; apply v4c_wp_exists_left; intro q848
  apply v4c_wp_exists_left; intro w864; apply v4c_wp_exists_left; intro w880
  apply v4c_wp_exists_left; intro w888
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have h8180 := v4c_step_2472_ok_to_8180 s4 (s0.sp - 2400#64) out
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc.epoch
    dw w160 d172 w192 w208 w224 w232
    q608 q624 q640 q656 q672 q688 q704 q720 q736 q752 q768 q784 q800 q816
    w832 q848 w864 w880 w888
    (memRegion (s0.sp - 2400#64 + 152#64) 8 ∗ memRegion (s0.sp - 2400#64 + 168#64) 4 ∗
     memRegion (s0.sp - 2400#64 + 176#64) 16 ∗ memRegion (s0.sp - 2400#64 + 200#64) 8 ∗
     memRegion (s0.sp - 2400#64 + 240#64) 368 ∗ memRegion (s0.sp - 2400#64 + 840#64) 8 ∗
     memRegion (s0.sp - 2400#64 + 871#64) 9 ∗ memRegion (s0.sp - 2400#64 + 895#64) 993 ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     memRegion (s0.sp - 2400#64 + 88#64) 40 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗
     v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
     v4c_decHeap A dec dw ∗ statesFromPbJumpTableAt b ∗ A.pool)
    hfsp_align hw0_lt hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h8180 ?_)
  intro s5 P5 hpc5 hrun5 hpost5
  rcases hpost5 with ⟨hP5, hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx5_5, hx6_5, hx7_5,
    hx8_5, hx9_5, hx10_5, hx11_5, hx12_5, hx13_5, hx14_5, hx15_5, hx16_5, hx17_5,
    hx18_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5,
    hx28_5, hx30_5, htr5⟩
  exact SepWP.weaken_pre (Entails.trans hP5 (Entails.of_eq (by ac_rfl)))
    (v4c_step_8180_ok_to_ret hA s0 s5 out pbA
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
      uc dec dw hsp0_align hpc5 hrun5 hsp5
      hx0_5 hx1_5 hx2_5 hx3_5 hx4_5 hx5_5 hx6_5 hx7_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hx13_5
      hx14_5 hx15_5 hx16_5 hx17_5 hx18_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5
      hx26_5 hx27_5 hx28_5 hx30_5 (htr5.trans htr4))

theorem v4c_step_2472_err_to_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (s0 s4 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (e : PolynomialError) (d32 : BitVec 64) (d28 : BitVec 32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 2472#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out) (hx22_4 : s4.readReg64 .x22 = dkCap)
    (hx26_4 : s4.readReg64 .x26 = rkPtr) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s4
      (resultPolyDecoderFromPbAt A (s0.sp - 2400#64 + 1888#64) (.error e) ∗
       memRegion (s0.sp - 2400#64 + 152#64) 64 ∗
       ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗
       memRegion (s0.sp - 2400#64 + 236#64) 1652 ∗
       stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
       memRegion (s0.sp - 2400#64 + 88#64) 40 ∗
       v4c_ucSpillSlots (s0.sp - 2400#64) ((ct1Len.extractLsb' 0 8).zeroExtend 64)
         mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
       memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
       memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
       v4b_ekSentCt1ReceivedHeap A
         rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
       statesFromPbJumpTableAt b ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have h8500 := v4c_step_2472_err_to_8500 (A := A) s4 (s0.sp - 2400#64) out dkCap rkPtr e
    (memRegion (s0.sp - 2400#64 + 152#64) 64 ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗
     memRegion (s0.sp - 2400#64 + 236#64) 1652 ∗
     stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     memRegion (s0.sp - 2400#64 + 88#64) 40 ∗
     v4c_ucSpillSlots (s0.sp - 2400#64) ((ct1Len.extractLsb' 0 8).zeroExtend 64)
       mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
     memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
     memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
     v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
     statesFromPbJumpTableAt b ∗ A.pool)
    hfsp_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx26_4
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h8500 ?_)
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx19_5, hx22_5, hx26_5, htr5⟩
  have hdealloc := v4c_ekSentCt1ReceivedHeap_entails_dealloc4 A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  have hstack_hook := v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hspill_eq := v4c_ucSpillSlots_eq_8500 (s0.sp - 2400#64)
    ((ct1Len.extractLsb' 0 8).zeroExtend 64)
    mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap
  have hdrop := v4_states_from_pb_drop_uc_8500 hA s0 s5 (s0.sp - 2400#64) out
    rkPtr rkCap mkPtr mkCap dkPtr dkCap ct1Ptr ct1Cap
    ((((s0.sp - 2400#64 + 32#64) ↦₆₄ (ct1Len.extractLsb' 0 8).zeroExtend 64) ∗
      ((s0.sp - 2400#64 + 40#64) ↦₆₄ mkLen) ∗ ((s0.sp - 2400#64 + 48#64) ↦₆₄ uc.epoch) ∗
      ((s0.sp - 2400#64 + 80#64) ↦₆₄ dkLen)) ∗
     memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗ memRegion (s0.sp - 2400#64 + 152#64) 64 ∗
     ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗
     memRegion (s0.sp - 2400#64 + 236#64) 1652 ∗
     memRegion ((s0.sp - 2400#64) - 5152#64) 1056 ∗
     memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
     memRegion (s0.sp - 2400#64 + 88#64) 40 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗
     statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b)
    hfsp_align hpc5 hrun5 hsp5 hx19_5 hx22_5 hx26_5 (htr5.trans htr4)
  refine SepWP.weaken_pre (Entails.trans hP5 ?_) (SepWP.seq hdrop ?_)
  · refine Entails.trans
      (Entails.of_eq (show _ =
        v4b_ekSentCt1ReceivedHeap A rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc ∗
        stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ((((s0.sp - 2400#64 + 56#64) ↦₆₄ rkCap) ∗
          ((s0.sp - 2400#64 + 72#64) ↦₆₄ ct1Ptr) ∗
          ((s0.sp - 2400#64 + 128#64) ↦₆₄ ct1Cap) ∗
          ((s0.sp - 2400#64 + 136#64) ↦₆₄ mkPtr) ∗
          ((s0.sp - 2400#64 + 144#64) ↦₆₄ dkPtr) ∗
          ((s0.sp - 2400#64 + 216#64) ↦₆₄ mkCap)) ∗
         (((s0.sp - 2400#64 + 32#64) ↦₆₄ (ct1Len.extractLsb' 0 8).zeroExtend 64) ∗
          ((s0.sp - 2400#64 + 40#64) ↦₆₄ mkLen) ∗
          ((s0.sp - 2400#64 + 48#64) ↦₆₄ uc.epoch) ∗
          ((s0.sp - 2400#64 + 80#64) ↦₆₄ dkLen)) ∗
         memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗ memRegion (s0.sp - 2400#64 + 152#64) 64 ∗
         ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗
         memRegion (s0.sp - 2400#64 + 236#64) 1652 ∗ memRegion (s0.sp - 2400#64) 32 ∗
         memRegion (s0.sp - 2400#64 + 64#64) 8 ∗ memRegion (s0.sp - 2400#64 + 88#64) 40 ∗
         memRegion (s0.sp - 2400#64 + 2288#64) 16 ∗ statesFromPbSavedCells s0 ∗
         memRegion out chunkedStatesSize ∗ memRegion pbA optProtoInnerStateSize ∗
         statesFromPbJumpTableAt b ∗ A.pool) by rw [hspill_eq]; ac_rfl))
      (Entails.trans (sepConj_mono hdealloc (sepConj_mono_left hstack_hook))
        (Entails.of_eq (by ac_rfl)))
  · intro s6 P6 hpc6 hrun6 ⟨hP6, hsp6, hx19_6, hx26_6, htr6⟩
    have hstack_col := v4c_err_8500_stack_collapse (s0.sp - 2400#64)
      ((ct1Len.extractLsb' 0 8).zeroExtend 64)
      mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap d32 d28
    have hstack_back := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have hx26_byte : (s6.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx26_6]; rfl
    have herr := v4_states_from_pb_err_5348 (A := A) (F := F) s0 s6 out .stateDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool)
      hsp0_align hpc6 hrun6 hsp6 hx19_6 hx26_byte htr6
    refine SepWP.weaken_pre (Entails.trans hP6 ?_) (SepWP.mono herr ?_)
    · refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (s0.sp - 2400#64) 32 ∗ memRegion (s0.sp - 2400#64 + 64#64) 8 ∗
           memRegion (s0.sp - 2400#64 + 88#64) 40 ∗ memRegion (s0.sp - 2400#64 + 152#64) 64 ∗
           v4c_ucSpillSlots (s0.sp - 2400#64) ((ct1Len.extractLsb' 0 8).zeroExtend 64)
             mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap ∗
           ((s0.sp - 2400#64 + 224#64) ↦₆₄ d32) ∗ ((s0.sp - 2400#64 + 232#64) ↦₃₂ d28) ∗
           memRegion (s0.sp - 2400#64 + 236#64) 1652 ∗
           memRegion (s0.sp - 2400#64 + 1888#64) 400 ∗ memRegion (s0.sp - 2400#64 + 2288#64) 16) ∗
          (stackAt (s0.sp - 2400#64) allocHookStack ∗ memRegion ((s0.sp - 2400#64) - 5152#64) 1056) ∗
          (statesFromPbSavedCells s0 ∗ memRegion out chunkedStatesSize ∗
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTableAt b ∗ A.pool) by
             rw [hspill_eq]; ac_rfl))
        (Entails.trans (sepConj_mono hstack_col (sepConj_mono_left hstack_back))
          (Entails.of_eq (by ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end CryptoVerification.SpqrV1.States.FromPb.Ext4K
