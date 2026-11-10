/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant4c0Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant9dPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbEk
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 4 (`EkSentCt1Received`, `+248`) — Part C

Relocatable Block-`333` post-`<PolyDecoder>::from_pb` continuations (`+2472 -> +8180 | +8500 -> ret`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

section

attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333

theorem v4c_step_8180_ok_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s5 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (dw : v4c_DecWords)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc5 : s5.pc = lsmpl.base 333 + 8180#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s5
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
         v4c_decHeap A dec dw ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)))
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
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
  have hep := states_from_pb_epilogue_8180_placed hA.memcpy s0 s5 out
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
     v4c_decHeap A dec dw ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
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
       statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) by ac_rfl))
    (Entails.trans (sepConj_mono_left hok) (Entails.of_eq (by ac_rfl)))

theorem v4c_step_2472_ok_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s4 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (dec : PolyDecoder) (dw : v4c_DecWords) (d32 : BitVec 64) (d28 : BitVec 32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 2472#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out)
    (hx20_4 : s4.readReg64 .x20 = (ct1Len.extractLsb' 8 32).zeroExtend 64)
    (hx21_4 : s4.readReg64 .x21 = (ct1Len.extractLsb' 56 8).zeroExtend 64)
    (hx22_4 : s4.readReg64 .x22 = dkCap)
    (hx23_4 : s4.readReg64 .x23 = (s0.sp - 2400#64) + 1888#64)
    (hx24_4 : s4.readReg64 .x24 = (ct1Len.extractLsb' 40 16).zeroExtend 64)
    (hx25_4 : s4.readReg64 .x25 = rkLen) (hx26_4 : s4.readReg64 .x26 = rkPtr)
    (hx27_4 : s4.readReg64 .x27 = (s0.sp - 2400#64) + 1792#64) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
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
         statesFromPbJumpTablePlacedAt ∗ A.pool)))
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out
            (.ok (.ekSentCt1Received { uc := uc, receiving_ct2 := dec })) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
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
  have h8180 := v4c_step_2472_ok_to_8180_placed (ext := ext) s4 (s0.sp - 2400#64) out
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
     v4c_decHeap A dec dw ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
    hfsp_align hw0_lt hpc4 hrun4 hsp4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h8180 ?_)
  intro s5 P5 hpc5 hrun5 hpost5
  rcases hpost5 with ⟨hP5, hsp5, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx5_5, hx6_5, hx7_5,
    hx8_5, hx9_5, hx10_5, hx11_5, hx12_5, hx13_5, hx14_5, hx15_5, hx16_5, hx17_5,
    hx18_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5,
    hx28_5, hx30_5, htr5⟩
  exact SepWP.weaken_pre (Entails.trans hP5 (Entails.of_eq (by ac_rfl)))
    (v4c_step_8180_ok_to_ret_placed hA s0 s5 out pbA
      rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len
      uc dec dw hsp0_align hpc5 hrun5 hsp5
      hx0_5 hx1_5 hx2_5 hx3_5 hx4_5 hx5_5 hx6_5 hx7_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hx13_5
      hx14_5 hx15_5 hx16_5 hx17_5 hx18_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5
      hx26_5 hx27_5 hx28_5 hx30_5 (htr5.trans htr4))

theorem v4c_step_2472_err_to_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext) (s0 s4 : State) (out pbA : BitVec 64)
    (rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len : BitVec 64)
    (uc : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F))
    (e : PolynomialError) (d32 : BitVec 64) (d28 : BitVec 32)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc4 : s4.pc = lsmpl.base 333 + 2472#64)
    (hrun4 : s4.status = .Running) (hsp4 : s4.sp = s0.sp - 2400#64)
    (hx19_4 : s4.readReg64 .x19 = out) (hx22_4 : s4.readReg64 .x22 = dkCap)
    (hx26_4 : s4.readReg64 .x26 = rkPtr) (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
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
       statesFromPbJumpTablePlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢
          resultChunkedStatesAt A (F := F) out (.error (.err .stateDecode)) ∗
          memRegion pbA optProtoInnerStateSize ∗
          statesFromPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesFromPbStack) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    sp_sub_2400_align s0.sp hsp0_align
  have h8500 := v4c_step_2472_err_to_8500_placed (A := A) (ext := ext) s4 (s0.sp - 2400#64) out dkCap rkPtr e
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
     statesFromPbJumpTablePlacedAt ∗ A.pool)
    hfsp_align hpc4 hrun4 hsp4 hx19_4 hx22_4 hx26_4
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.seq h8500 ?_)
  intro s5 P5 hpc5 hrun5 ⟨hP5, hsp5, hx19_5, hx22_5, hx26_5, htr5⟩
  have hdealloc := v4c_ekSentCt1ReceivedHeap_entails_dealloc4 A (F := F)
    rkCap rkPtr rkLen mkCap mkPtr mkLen dkCap dkPtr dkLen ct1Cap ct1Ptr ct1Len uc
  have hstack_hook := v4_stackAt_encoderFromPbStack_to_allocHook (s0.sp - 2400#64)
  have hspill_eq := v4c_ucSpillSlots_eq_8500 (s0.sp - 2400#64)
    ((ct1Len.extractLsb' 0 8).zeroExtend 64)
    mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap
  have hdrop := v4_states_from_pb_drop_uc_8500_placed hA s0 s5 (s0.sp - 2400#64) out
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
     memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt)
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
         statesFromPbJumpTablePlacedAt ∗ A.pool) by rw [hspill_eq]; ac_rfl))
      (Entails.trans (sepConj_mono hdealloc (sepConj_mono_left hstack_hook))
        (Entails.of_eq (by ac_rfl)))
  · intro s6 P6 hpc6 hrun6 ⟨hP6, hsp6, hx19_6, hx26_6, htr6⟩
    have hstack_col := v4c_err_8500_stack_collapse (s0.sp - 2400#64)
      ((ct1Len.extractLsb' 0 8).zeroExtend 64)
      mkLen uc.epoch rkCap ct1Ptr dkLen ct1Cap mkPtr dkPtr mkCap d32 d28
    have hstack_back := v4_stackAt_allocHook_to_encoderFromPbStack (s0.sp - 2400#64)
    have hx26_byte : (s6.readReg64 .x26).extractLsb' 0 8 = spqrErrorByte .stateDecode := by
      rw [hx26_6]; rfl
    have herr := v4_states_from_pb_err_5348_placed (A := A) (F := F) (ext := ext) s0 s6 out .stateDecode
      (memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool)
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
           memRegion pbA optProtoInnerStateSize ∗ statesFromPbJumpTablePlacedAt ∗ A.pool) by
             rw [hspill_eq]; ac_rfl))
        (Entails.trans (sepConj_mono hstack_col (sepConj_mono_left hstack_back))
          (Entails.of_eq (by ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

end

section EkFromPb

set_option hygiene false
attribute [local irreducible]
  Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero extractLsb'_0_64_append extractLsb'_64_64_append

@[local arm64_norm] private theorem v4c_sub_beq_zero_eq_beq (x y : BitVec 64) :
    (x - y == 0#64) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have hne : x - y ≠ 0#64 := by intro h0; apply h; bv_omega
    simp [h, hne]

@[local arm64_norm] private theorem v4c_bne_eq_not_beq (x y : BitVec 64) : (x != y) = !(x == y) := rfl

private theorem v4c_sepWPp_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q_regs sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm → SepWPp prog ret sm P_mid Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h1 fun sm _ hpc hrun hclm ⟨hent, hq⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hclm hq))

private theorem v4c_onPanic_frame_entails {s0 sm sf : State} {F : SepProp}
    (htrace : sm.trace = s0.trace) :
    (⌜allocFailedIn sm sf ∧ sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  rw [sepConj_assoc]; apply Entails.pure_left; intro ⟨haf, hpref⟩
  unfold allocFailedIn at haf ⊢; rw [htrace] at haf hpref
  exact Entails.pure_right ⟨haf, hpref⟩ (entails_anyHeap _)

private theorem v4c_sepWPp_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (h : φ → SepWPp prog ret s P' Q Qp oom) (hf : P = ⌜φ⌝ ∗ P' := by sep_focus) :
    SepWPp prog ret s P Q Qp oom := by
  rw [hf]; exact SepWPp.pure_left h

private theorem v4c_sepWPp_call_ret {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P_step F R : SepProp} {Qpan : State → SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P_step ∗ R') → (s.mem ⊨ spec.pre x s ∗ R'))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → SepWP prog target_pc sf (spec.post x s sf ∗ F) post)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog target_pc s (P_step ∗ F) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => by rw [sepConj_assoc] at hm; exact hpre (F ∗ R') hm)
    (fun sf code R' _ hm => by rw [hexit_eq] at hm; exact not_satisfies_false_sepConj hm)
    (fun sf _ hm => Satisfies.mono (sepConj_mono_left (hpan sf)) hm)
    (fun sf hpcf hrunf hspf hcsf => SepWPp.of_sepWP_ret (hnext sf hpcf hrunf hspf hcsf))
    (fun sf _ _ hm => False.elim (by rw [hoom_eq] at hm; exact not_satisfies_false_sepConj hm))

private theorem v4c_sepWP_pure_elim_focus {prog : Program} {ret : BitVec 64} {s : State}
    (φ : Prop) {P Rest : SepProp} {Q : State → SepProp → Prop}
    (h : φ → SepWP prog ret s Rest Q) (heq : P = ⌜φ⌝ ∗ Rest := by sep_focus) :
    SepWP prog ret s P Q := by
  rw [heq]; exact SepWP.pure_elim h

local macro "saved48S0" sp:term "," s0:term : term =>
  `((($sp - 48#64) ↦₆₄ ($s0).readReg64 .fp) ∗ (($sp - 40#64) ↦₆₄ ($s0).readReg64 .lr) ∗
    (($sp - 32#64) ↦₆₄ ($s0).readReg64 .x22) ∗ (($sp - 24#64) ↦₆₄ ($s0).readReg64 .x21) ∗
    (($sp - 16#64) ↦₆₄ ($s0).readReg64 .x20) ∗ (($sp - 8#64) ↦₆₄ ($s0).readReg64 .x19))
local macro "saved48Vars" sp:term "," fp:term "," lr:term "," x22:term "," x21:term "," x20:term "," x19:term : term =>
  `((($sp - 48#64) ↦₆₄ $fp) ∗ (($sp - 40#64) ↦₆₄ $lr) ∗ (($sp - 32#64) ↦₆₄ $x22) ∗
    (($sp - 24#64) ↦₆₄ $x21) ∗ (($sp - 16#64) ↦₆₄ $x20) ∗ (($sp - 8#64) ↦₆₄ $x19))

private theorem v4c_authenticatorPBPinnedAt_48_entails_dealloc (A : RustAlloc)
    (ga : AuthenticatorPBGhost) (a : BitVec 64) (auth : ProtoAuthenticator) :
    authenticatorPBPinnedAt A ga (a + 48#64) auth ⊢
      Drop.auth48HeadersAt a ⟨ga.rootKey, ga.macKey⟩ ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr := by
  rw [← Drop.twoVecHeadersAt_48_eq]; exact authenticatorPBPinnedAt_entails_dealloc A ga (a + 48#64) auth

private theorem v4c_protoUnchunked2VecHeadersAt_entails_memRegion_104 (a : BitVec 64) (g : TwoVecGhost) :
    protoUnchunked2VecHeadersAt a g ∗ memRegion (a + 48#64) 48 ∗ memRegion (a + 96#64) 8 ⊢ memRegion a 104 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 48) (k := 56) (b' := a + 48#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 48) (k := 8) (b' := a + 96#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (twoVecHeadersAt_entails_memRegion_48 a g)

private theorem v4c_authenticatorAt_sub144_unpack (A : RustAlloc) (sp : BitVec 64) (auth : Authenticator) :
    authenticatorAt A (sp - 144#64) auth ⊢
      ∃∗ ca1 : BitVec 64, ∃∗ pa1 : BitVec 64, ∃∗ ca2 : BitVec 64, ∃∗ pa2 : BitVec 64,
        (((sp - 144#64) ↦₆₄ ca1) ∗ ((sp - 136#64) ↦₆₄ pa1) ∗ ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
         ((sp - 120#64) ↦₆₄ ca2) ∗ ((sp - 112#64) ↦₆₄ pa2) ∗ ((sp - 104#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)) ∗
        vecU8Payload A ca1 pa1 auth.rootKey ∗ vecU8Payload A ca2 pa2 auth.macKey := by
  have h := authenticatorAt_unpack A (sp - 144#64) auth
  have h1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  have h3 : (sp - 144#64) + 24#64 = sp - 120#64 := by bv_omega
  have h4 : (sp - 144#64) + 32#64 = sp - 112#64 := by bv_omega
  have h5 : (sp - 144#64) + 40#64 = sp - 104#64 := by bv_omega
  rwa [h1, h2, h3, h4, h5] at h

private theorem v4c_memRegion_144_96_split_48_48 (sp : BitVec 64) :
    memRegion (sp - 144#64) 96 = memRegion (sp - 144#64) 48 ∗ memRegion (sp - 96#64) 48 :=
  ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 48) (b' := sp - 96#64) rfl (by bv_omega) (by decide)

local macro "ekTail" A:term "," s0:term : term =>
  `(($A).pool ∗ memRegion (($s0).sp - 4304#64) 64 ∗ stackAt (($s0).sp - 144#64) allocHookStack ∗
    memRegion (($s0).sp - 144#64) 96 ∗ (saved48S0 ($s0).sp, $s0))
local macro "ekOutNone" out:term : term =>
  `(($out ↦₆₄ noneCap) ∗ (($out + 8#64) ↦₈ 0#8) ∗ memRegion ($out + 9#64) 95)
local macro "ekVecs" A:term "," pbA:term "," pb:term "," c1:term "," p1:term "," c2:term "," p2:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).dk.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    (($pbA + 96#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).dk ∗ vecU8Payload $A $c2 $p2 ($pb).ct1)
local macro "ekUnpacked" A:term "," pbA:term "," pb:term "," authOpt:term "," c1:term "," p1:term "," c2:term "," p2:term : term =>
  `(($pbA ↦₆₄ $c1) ∗ (($pbA + 8#64) ↦₆₄ $p1) ∗ (($pbA + 16#64) ↦₆₄ BitVec.ofNat 64 ($pb).dk.length) ∗
    (($pbA + 24#64) ↦₆₄ $c2) ∗ (($pbA + 32#64) ↦₆₄ $p2) ∗ (($pbA + 40#64) ↦₆₄ BitVec.ofNat 64 ($pb).ct1.length) ∗
    $authOpt ∗ (($pbA + 96#64) ↦₆₄ ($pb).epoch) ∗ vecU8Payload $A $c1 $p1 ($pb).dk ∗ vecU8Payload $A $c2 $p2 ($pb).ct1)

set_option maxHeartbeats 800000 in
private theorem v4c_ek_sent_ct1_received_from_pb_err_drop_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ optProtoAuthenticatorAt A (pbA + 48#64) pb.auth ∗
          memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, Bool.false_eq_true, ↓reduceIte, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine Drop.seq_clean (mid := (blkPl_348).base + 236#64)
    (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
      memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · cases pb.auth with
    | none =>
      rw [Drop.optProtoAuthenticatorAt_48_none]
      have hstep : SepWP ((blkPC_348).rebase (blkPl_348).base H) ((blkPl_348).base + 236#64) s1
          (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗ (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
          (fun sm Pm => (Pm ⊢ ((ekOutNone out) ∗
            (protoUnchunked2VecHeadersAt pbA g ∗ (((pbA + 48#64) ↦₆₄ noneCap) ∗ memRegion (pbA + 56#64) 40) ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)) ∧
            Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
        wp_steps; refine Drop.align_pre (by dsimp only [noneCap]) ?_; wp_done
      exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (Drop.optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA))))) hstep
    | some a =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_left (protoAuthenticatorAt_entails_dealloc A (pbA + 48#64) a))))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left, sepExists_sepConj_right]
      apply ProofLib.SepWP.exists_left; intro ga; rw [Drop.twoVecHeadersAt_48_eq]
      apply v4c_sepWP_pure_elim_focus (ga.v1.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      refine Drop.seq_clean (mid := (blkPl_348).base + 216#64)
        (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗
          (Drop.auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · dsimp only [Drop.auth48HeadersAt, vecCapPtrDealloc]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine align_pre (by dsimp only [noneCap]; ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
      · intro sa1 hpca1 hruna1 ⟨⟨hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hsp_a1, htrace_a1⟩, hx19_a1⟩
        have hstepa2 : SepWP ((blkPC_348).rebase (blkPl_348).base H) ((blkPl_348).base + 236#64) sa1
            ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗
              (Drop.auth48HeadersAt pbA ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗ memRegion (pbA + 96#64) 8 ∗
              vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
            (fun sm Pm => (Pm ⊢ ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ Drop.auth48HeadersAt pbA ga ∗
              memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)) ∧
              Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) := by
          dsimp only [Drop.auth48HeadersAt, vecCapPtrDealloc]
          by_cases hca2 : (ga.v2.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_a1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right
          (sepConj_mono_left (Drop.auth48HeadersAt_entails_memRegion_48 pbA ga))))) hstepa2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    refine Drop.seq_clean (mid := (blkPl_348).base + 256#64)
      (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
        memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (v4c_protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
              unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
            (sepConj_mono_left (v4c_protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

private theorem v4c_ek_sent_ct1_received_from_pb_err_drop_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false)
    (hpc1 : s1.pc = (blkPl_348).base + 176#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) pb.auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
      (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch pb.auth pb.dk pb.ct1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (v4c_ek_sent_ct1_received_from_pb_err_drop_placed (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 800000 in
private theorem v4c_ek_sent_ct1_received_from_pb_auth_none_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    {v_out0 : BitVec 64} {v_out8 : BitVec 8} {g : TwoVecGhost}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (((out ↦₆₄ v_out0) ∗ ((out + 8#64) ↦₈ v_out8) ∗ memRegion (out + 9#64) 95) ∗
        (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0)
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine Drop.seq_clean (mid := (blkPl_348).base + 328#64)
    (P_mid := ((ekOutNone out) ∗ (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗
      memRegion (pbA + 96#64) 8 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
  · dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by dsimp only [noneCap]) ?_; wp_done
    · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; dsimp only [noneCap]; ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2⟩
    dsimp only [protoUnchunked2VecHeadersAt, twoVecHeadersAt, vecCapPtrDealloc]
    by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (v4c_protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
      rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
    · wp_steps
      refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
        (Entails.trans (Entails.of_eq (show _ =
          (protoUnchunked2VecHeadersAt pbA g ∗ memRegion (pbA + 48#64) 48 ∗ memRegion (pbA + 96#64) 8) ∗
          (A.live g.v2.ptr g.v2.cap.toNat 1 ∗ memRegion g.v2.ptr g.v2.cap.toNat) by
            unfold protoUnchunked2VecHeadersAt twoVecHeadersAt; ac_rfl))
          (sepConj_mono_left (v4c_protoUnchunked2VecHeadersAt_entails_memRegion_104 pbA g)))
        (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
      wp_apply; wp_done

private theorem v4c_ek_sent_ct1_received_from_pb_auth_none_unpacked_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = none)
    (hpc1 : s1.pc = (blkPl_348).base + 296#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx0_1 : s1.readReg64 .x0 = out) (hx19_1 : s1.readReg64 .x19 = pbA)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) none), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
  refine SepWP.weaken_pre (sepConj_mono (memRegion_104_err_split out)
    (sepConj_mono_left (Entails.trans
      (unpacked_ekSentCt1Received_entails_dealloc A pbA c1 p1
        (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch none pb.dk pb.ct1)
      (sepConj_mono_right (sepConj_mono_left (by
        rw [Drop.optProtoAuthenticatorAt_48_none]; exact Drop.optProtoAuthenticatorAt_48_none_entails_memRegion_48 A pbA)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left; intro v_out0; apply ProofLib.SepWP.exists_left; intro v_out8
  exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (v4c_ek_sent_ct1_received_from_pb_auth_none_placed (v_out0 := v_out0) (v_out8 := v_out8) (g := ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩)
      hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align)

set_option maxHeartbeats 1200000 in
private theorem v4c_ek_sent_ct1_received_from_pb_ok_after_auth_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {H : String → Option (State → State)} {out pbA c1 p1 c2 p2 : BitVec 64}
    {pb : V1State.Unchunked.EkSentCt1Received} {auth : ProtoAuthenticator}
    {ga : AuthenticatorPBGhost} {R : SepProp} {s0 s1 : State}
    (hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true)
    (hauth : pb.auth = some auth)
    (hpc1 : s1.pc = (blkPl_348).base + 80#64) (hrun1 : s1.status = .Running)
    (hpres1 : Saved48Preserved s0 s1 (s0.sp - 144#64))
    (hx19_1 : s1.readReg64 .x19 = pbA) (hx20_1 : s1.readReg64 .x20 = ga.rootKey.cap)
    (hx21_1 : s1.readReg64 .x21 = pb.epoch) (hx22_1 : s1.readReg64 .x22 = out)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true) :
    SepWP ((blkPC_348).rebase (blkPl_348).base H) (s0.readReg64 .lr) s1
      (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (authenticatorPBPinnedAt A ga (pbA + 48#64) auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗
        authenticatorAt A (s0.sp - 144#64) (Authenticator.fromPb auth) ∗ memRegion (s0.sp - 96#64) 48 ∗ (saved48S0 s0.sp, s0))
      (WppPostEk (ekSentCt1ReceivedFromPbSpec A F) ⟨out, pbA, pb⟩ R s0) := by
  simp only [WppPostEk, ekSentCt1ReceivedFromPbSpec, Unchunked.SendEk.EkSentCt1Received.from_pb,
    hcond, hauth, ↓reduceIte, spqrAuthApi, ekSentCt1ReceivedResultAt, stackAt_ekSentCt1ReceivedFromPb_split_allocHook, rustDeallocSpec] at hdealloc_raw ⊢
  rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩
  refine Drop.seq_clean (mid := (blkPl_348).base + 140#64)
    (P_mid := (ekSentCt1ReceivedAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
      (memRegion pbA 48 ∗ Drop.auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
        vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ekTail A, s0))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap) ?_ ?_
  · refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (v4c_authenticatorPBPinnedAt_48_entails_dealloc A ga pbA auth))))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (v4c_authenticatorAt_sub144_unpack A s0.sp (Authenticator.fromPb auth))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply ProofLib.SepWP.exists_left; intro ca1; apply ProofLib.SepWP.exists_left; intro pa1
    apply ProofLib.SepWP.exists_left; intro ca2; apply ProofLib.SepWP.exists_left; intro pa2
    rw [ProofLib.memRegion_cells (s0.sp - 96#64) 6 (by decide), memRegion_104_eq_cells13 out]
    cells_unfold
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepExists_sepConj_right]
    wp_pull_exists; wp_steps; rw [stackAt_authFromPb_split_allocHook_sub144 s0.sp]
    have hpack_out := ekSentCt1ReceivedAt_pack A (F := F) out ca1 pa1 ca2 pa2 c1 p1 c2 p2 pb.epoch (Authenticator.fromPb auth) pb.dk pb.ct1
    have hpack_sp := memRegion_ekSentCt1Received_scratch_restore s0.sp ca1 pa1 (BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length)
      ca2 pa2 (BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length)
    have hpack_pb := unpacked_ekSentCt1Received_headers_entails_memRegion_48_8 pbA c1 p1 (BitVec.ofNat 64 pb.dk.length) c2 p2 (BitVec.ofNat 64 pb.ct1.length) pb.epoch
    refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
      (((out ↦₆₄ ca1) ∗ ((out + 8#64) ↦₆₄ pa1) ∗ ((out + 16#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((out + 24#64) ↦₆₄ ca2) ∗ ((out + 32#64) ↦₆₄ pa2) ∗ ((out + 40#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length) ∗
        ((out + 48#64) ↦₆₄ c1) ∗ ((out + 56#64) ↦₆₄ p1) ∗ ((out + 64#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((out + 72#64) ↦₆₄ c2) ∗ ((out + 80#64) ↦₆₄ p2) ∗ ((out + 88#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((out + 96#64) ↦₆₄ pb.epoch)) ∗
       vecU8Payload A ca1 pa1 (Authenticator.fromPb auth).rootKey ∗ vecU8Payload A ca2 pa2 (Authenticator.fromPb auth).macKey ∗
       vecU8Payload A c1 p1 pb.dk ∗ vecU8Payload A c2 p2 pb.ct1) ∗
      (((pbA ↦₆₄ c1) ∗ ((pbA + 8#64) ↦₆₄ p1) ∗ ((pbA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((pbA + 24#64) ↦₆₄ c2) ∗ ((pbA + 32#64) ↦₆₄ p2) ∗ ((pbA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length) ∗ ((pbA + 96#64) ↦₆₄ pb.epoch)) ∗
       Drop.auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ vecCapPtrDealloc A ga.rootKey.cap ga.rootKey.ptr ∗ vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗
      ((((s0.sp - 144#64) ↦₆₄ ca1) ∗ ((s0.sp - 136#64) ↦₆₄ pa1) ∗ ((s0.sp - 128#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).rootKey.length) ∗
        ((s0.sp - 120#64) ↦₆₄ ca2) ∗ ((s0.sp - 112#64) ↦₆₄ pa2) ∗ ((s0.sp - 104#64) ↦₆₄ BitVec.ofNat 64 (Authenticator.fromPb auth).macKey.length)) ∗
       (((s0.sp - 96#64) ↦₆₄ c1) ∗ ((s0.sp - 88#64) ↦₆₄ p1) ∗ ((s0.sp - 80#64) ↦₆₄ BitVec.ofNat 64 pb.dk.length) ∗
        ((s0.sp - 72#64) ↦₆₄ c2) ∗ ((s0.sp - 64#64) ↦₆₄ p2) ∗ ((s0.sp - 56#64) ↦₆₄ BitVec.ofNat 64 pb.ct1.length))) ∗
      A.pool ∗ memRegion (s0.sp - 4304#64) 64 ∗ stackAt (s0.sp - 144#64) allocHookStack ∗ (saved48S0 s0.sp, s0) by ac_rfl))
      (sepConj_mono hpack_out (sepConj_mono (sepConj_mono_left hpack_pb) (sepConj_mono_left hpack_sp)))) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩, hx19_2, hx20_2⟩
    refine Drop.seq_clean (mid := (blkPl_348).base + 160#64)
      (P_mid := (ekSentCt1ReceivedAt A (F := F) out { epoch := pb.epoch, auth := Authenticator.fromPb auth, dk := pb.dk, ct1 := pb.ct1 } ∗
        (memRegion pbA 48 ∗ Drop.auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8 ∗
          vecCapPtrDealloc A ga.macKey.cap ga.macKey.ptr) ∗ ekTail A, s0))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · dsimp only [Drop.auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca1 : (ga.rootKey.cap == 0#64) = true <;> simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; wp_done
      · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
    · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩, hx19_3⟩
      dsimp only [Drop.auth48HeadersAt, vecCapPtrDealloc]
      by_cases hca2 : (ga.macKey.cap == 0#64) = true <;> simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_restore_from_allocHook s0.sp _ _ _ _ _ _)))) ?_
        rw [stackAt_ekSentCt1ReceivedFromPb_split_allocHook s0.sp]; wp_done
      · wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono
          (Entails.trans (Entails.of_eq (show _ =
            (memRegion pbA 48 ∗ Drop.auth48HeadersAt pbA ⟨ga.rootKey, ga.macKey⟩ ∗ memRegion (pbA + 96#64) 8) ∗
            (A.live ga.macKey.ptr ga.macKey.cap.toNat 1 ∗ memRegion ga.macKey.ptr ga.macKey.cap.toNat) by unfold Drop.auth48HeadersAt; ac_rfl))
            (sepConj_mono_left (memRegion_48_auth48_8_entails_104 pbA ⟨ga.rootKey, ga.macKey⟩)))
          (sepConj_mono_right (stackAt_ekSentCt1ReceivedFromPb_tail_allocHook s0.sp _ _ _ _ _ _)))) ?_
        wp_apply; wp_done

set_option maxHeartbeats 1200000 in
theorem v4c_ek_sent_ct1_received_from_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_348 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) := by
  rw [← ls_blockPlacement_base (i := 348)]
  change subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext)) (blkPl_348).base _
  have hdealloc_raw : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) := spqr_hook_ok_of_mem hA.dealloc
  have hauth_cl : subroutine_ok ((blkPC_348).rebase (blkPl_348).base (Rust.withPanics ext))
      (lsmpl.base 330) (withLsCodeLoaded lsmpl (authFromPbPinnedSpec A)) :=
    Variant9dPlaced.v9_auth_from_pb_pinned_cl_on hA
  apply subroutine_ok_of_sepWPp
  intro ⟨out, pbA, pb⟩ R s0 hpc hrun hpre hsp_align
  have hsp_align_bv : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  have ⟨hm0, hx0, hx1⟩ : s0.mem ⊨ (memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
      A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack) ∗ R ∧ s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = pbA := by
    simp only [ekSentCt1ReceivedFromPbSpec] at hpre; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; exact ⟨hpre.2, hpre.1⟩
  refine ⟨memRegion out 104 ∗ protoUnchunkedEkSentCt1ReceivedAt A pbA pb ∗
    A.pool ∗ stackAt s0.sp ekSentCt1ReceivedFromPbStack, R, hm0, ?_⟩
  rw [stackAt_ekSentCt1ReceivedFromPb_split s0.sp]
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (protoUnchunkedEkSentCt1ReceivedAt_unpack A pbA pb))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro c1; apply SepWPp.exists_elim; intro p1
  apply SepWPp.exists_elim; intro c2; apply SepWPp.exists_elim; intro p2
  apply v4c_sepWPp_pure_elim_focus (pb.dk.length < 2 ^ 63 ∧ pb.ct1.length < 2 ^ 63 ∧ c1.toNat < 2 ^ 63)
  intro ⟨hl1, hl2, _⟩; cells_unfold
  apply SepWPp.exists_elim; intro fp_old; apply SepWPp.exists_elim; intro lr_old
  apply SepWPp.exists_elim; intro x22_old; apply SepWPp.exists_elim; intro x21_old
  apply SepWPp.exists_elim; intro x20_old; apply SepWPp.exists_elim; intro x19_old
  by_cases hcond : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = true
  · have hdk_t : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true := by
      rw [ofNat_beq_lit_iff hl1 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.1
    have hct1_t : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true := by
      rw [ofNat_beq_lit_iff hl2 (by decide)]; simp only [Bool.and_eq_true] at hcond; exact hcond.2
    cases hauth : pb.auth with
    | none =>
      apply SepWPp.of_sepWP_ret; rw [Drop.optProtoAuthenticatorAt_48_none]
      refine Drop.seq_clean (mid := (blkPl_348).base + 296#64)
        (P_mid := (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) none), c1, p1, c2, p2) ∗
          A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0)))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
      · wp_steps; rw [Drop.optProtoAuthenticatorAt_48_none]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19, noneCap]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
        exact v4c_ek_sent_ct1_received_from_pb_auth_none_unpacked_placed hdealloc_raw hcond hauth hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv
    | some auth =>
      refine SepWPp.weaken_pre (Entails.trans (Entails.of_eq (show _ =
        optProtoAuthenticatorAt A (pbA + 48#64) (some auth) ∗
        (memRegion out 104 ∗ (ekVecs A, pbA, pb, c1, p1, c2, p2) ∗
         A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗
         saved48Vars s0.sp, fp_old, lr_old, x22_old, x21_old, x20_old, x19_old) by ac_rfl))
        (sepConj_mono_left (optProtoAuthenticatorAt_some_unpack A (pbA + 48#64) auth))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply SepWPp.exists_elim; intro ga
      apply v4c_sepWPp_pure_elim_focus (ga.rootKey.cap.toNat < 2 ^ 63); intro hga_lt
      have hne_none := cap_add_one_beq_zero_false hga_lt
      rw [v4c_memRegion_144_96_split_48_48 s0.sp]
      refine v4c_sepWPp_seq_clean_lscl hcl (mid := lsmpl.base 330)
        (P_mid := (memRegion (s0.sp - 144#64) 48 ∗ authenticatorPBPinnedAt A ga (pbA + 48#64) auth ∗
          A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack) ∗
          (memRegion out 104 ∗ (ekVecs A, pbA, pb, c1, p1, c2, p2) ∗ memRegion (s0.sp - 96#64) 48 ∗ (saved48S0 s0.sp, s0)))
        (Q_regs := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧
          sm.readReg64 .x0 = s0.sp - 144#64 ∧ sm.readReg64 .x1 = pbA + 48#64 ∧ sm.readReg64 .lr = (blkPl_348).base + 80#64 ∧
          sm.readReg64 .x19 = pbA ∧ sm.readReg64 .x20 = ga.rootKey.cap ∧ sm.readReg64 .x21 = pb.epoch ∧ sm.readReg64 .x22 = out) ?_ ?_
      · wp_steps
        rw [← sepConj_assoc ((pbA + 48#64) ↦₆₄ ga.rootKey.cap), ← authenticatorPBPinnedAt_eq_cap_tail A ga (pbA + 48#64) auth]
        refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · intro sm hpcm hrunm hclm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx0_m, hx1_m, hlr_m, hx19_m, hx20_m, hx21_m, hx22_m⟩
        have hsp_align_m : sm.spAligned = true := by
          simp only [State.spAligned, hsp_m, sp_and_15_sub_aligned s0.sp 144#64 (by decide)]; exact hsp_align_bv
        refine v4c_sepWPp_call_ret hauth_cl (x := ⟨s0.sp - 144#64, pbA + 48#64, ga, auth⟩)
          hpcm hrunm hsp_align_m hlr_m ?_ ?_ (fun _ _ => rfl) ?_
        · intro R' hm'; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]; refine ⟨hclm, ?_⟩
          rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0_m, hx1_m⟩, Satisfies.mono (Entails.of_eq (by rw [hsp_m])) hm'⟩
        · intro sf; dsimp only [withLsCodeLoaded, authFromPbPinnedSpec, ekSentCt1ReceivedFromPbSpec]
          exact v4c_onPanic_frame_entails htrace_m
        · intro s1 hpc1 hrun1 hsp1 ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
          rw [hx19_m] at hx19_1; rw [hx20_m] at hx20_1; rw [hx21_m] at hx21_1; rw [hx22_m] at hx22_1
          rw [hx23_m] at hx23_1; rw [hx24_m] at hx24_1; rw [hx25_m] at hx25_1; rw [hx26_m] at hx26_1
          rw [hx27_m] at hx27_1; rw [hx28_m] at hx28_1; rw [hsp_m] at hsp1
          dsimp only [withLsCodeLoaded, authFromPbPinnedSpec]
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply ProofLib.SepWP.pure_elim; intro htrace_s1; rw [htrace_m] at htrace_s1
          exact SepWP.weaken_pre (Entails.of_eq (by rw [hsp_m]; ac_rfl))
            (v4c_ek_sent_ct1_received_from_pb_ok_after_auth_placed hdealloc_raw hcond hauth hpc1 hrun1
              ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp1, htrace_s1, hvregs_1.trans hvregs_m⟩
              hx19_1 hx20_1 hx21_1 hx22_1 hsp_align_bv)
  · apply SepWPp.of_sepWP_ret
    have hcond_f : (pb.dk.length == DECAPSULATION_KEY_SIZE && pb.ct1.length == CIPHERTEXT1_SIZE) = false := Bool.eq_false_iff.mpr hcond
    refine Drop.seq_clean (mid := (blkPl_348).base + 176#64)
      (P_mid := (memRegion out 104 ∗ (ekUnpacked A, pbA, pb, (optProtoAuthenticatorAt A (pbA + 48#64) pb.auth), c1, p1, c2, p2) ∗
        A.pool ∗ stackAt (s0.sp - 144#64) authFromPbStack ∗ memRegion (s0.sp - 144#64) 96 ∗ (saved48S0 s0.sp, s0)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 144#64) ∧ sm.readReg64 .x0 = out ∧ sm.readReg64 .x19 = pbA) ?_ ?_
    · by_cases h1 : (BitVec.ofNat 64 pb.dk.length == 2400#64) = true
      · by_cases h2 : (BitVec.ofNat 64 pb.ct1.length == 960#64) = true
        · exfalso; apply hcond
          rw [ofNat_beq_lit_iff hl1 (by decide)] at h1; rw [ofNat_beq_lit_iff hl2 (by decide)] at h2
          simp [h1, h2, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE]
        · have h2_f : (BitVec.ofNat 64 pb.ct1.length == 960#64) = false := Bool.eq_false_iff.mpr h2
          wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
      · have h1_f : (BitVec.ofNat 64 pb.dk.length == 2400#64) = false := Bool.eq_false_iff.mpr h1
        wp_steps; refine align_pre (by dsimp only [Reg.fp, Reg.lr, Reg.x22, Reg.x21, Reg.x20, Reg.x19]; ac_rfl) ?_; wp_done
    · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1, hx19_1⟩
      exact v4c_ek_sent_ct1_received_from_pb_err_drop_unpacked_placed hdealloc_raw hcond_f hpc1 hrun1 hpres1 hx0_1 hx19_1 hsp_align_bv

theorem v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)} (hA : FromPbAllocHooks A ext) :
    subroutine_ok (lsProg_333 (Rust.withPanics ext)) (lsmpl.base 348)
      (withLsCodeLoaded lsmpl (ekSentCt1ReceivedFromPbSpec A F)) :=
  ls_subroutine_ok_of_block (v4c_ek_sent_ct1_received_from_pb_cl_placed_ok hA)

end EkFromPb

end LibsignalBinary.Proofs.SpqrV1.States.FromPb

namespace CryptoVerification.SpqrV1.States.FromPb
export LibsignalBinary.Proofs.SpqrV1.States.FromPb (
  v4c_step_8180_ok_to_ret_placed
  v4c_step_2472_ok_to_ret_placed
  v4c_step_2472_err_to_ret_placed
  v4c_ek_sent_ct1_received_from_pb_cl_placed_ok
  v4c_ek_sent_ct1_received_from_pb_on_333_placed_ok)
end CryptoVerification.SpqrV1.States.FromPb
