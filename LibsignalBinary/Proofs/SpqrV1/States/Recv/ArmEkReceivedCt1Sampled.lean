/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekReceivedCt1Sampled` Arm

Verifies the `.ekReceivedCt1Sampled` match arm (`entry + 3392`, tag `10#64`) of `<States>::recv`,
parameterized by `EkRecvMode` (`states_recv_ekReceivedCt1Sampled_sepWPp_gen` and `_ok_ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.States.Leaves

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## Top-Level Proof of `.ekReceivedCt1Sampled` (Tag `10#64`) -/

theorem ek_gt_3732_ret
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext) (s0 s : State) (outA selfA msg_ep : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (P_rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 3732#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 4240#64) (hz : s.pstate.z = false)
    (hx8 : s.readReg64 .x8 = BitVec.zeroExtend 64 1#32) (hx0 : s.readReg64 .x0 = selfA + 8#64)
    (hx19 : s.readReg64 .x19 = outA) (hx25 : s.readReg64 .x25 = msg_ep) (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 10#64) ∗
        chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
        A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          memRegion selfA chunkedStatesSize ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  rw [memRegion_out_960_split_err outA, stackAt_statesRecvCallee_eq_dropStack32 (s0.sp - 4240#64)]
  wp_pull_exists; rename_i u16 u8 u0
  refine seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 19324#64)
    (P_mid := stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗ (P_rest ∗
       resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
       memRegion selfA chunkedStatesSize ∗ A.pool))
    (Q := fun sm => sm.sp = s0.sp - 4240#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
  · have hstep := ek_step_3732_gt_19324 hdealloc s (s0.sp - 4240#64) outA selfA msg_ep u0 u16 u8 st
      (P_rest ∗ memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
       (selfA ↦₆₄ 10#64) ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion ((s0.sp - 4240#64) - 19552#64) 15424 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hz hx8 hx0 hx19 hx25
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro sm Pm _ _ ⟨hPm, hsp_m, htr_m⟩
    refine ⟨Entails.trans hPm ?_, hsp_m, htr_m.trans htr⟩
    have herr := err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg_ep
    have hself := selfA_528_entails_memRegion selfA
    rw [stackAt_statesRecvCallee_eq_dropStack32 (s0.sp - 4240#64)]
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 4240#64) - 19552#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropStack32) ∗
      memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗
      (P_rest ∗ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
        memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
       ((selfA ↦₆₄ 10#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392) ∗
       A.pool) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono herr (sepConj_mono_left hself)))))
  · intro sm hpcm hrunm ⟨hsp_m, htr_m⟩
    refine SepWP.mono
      (states_recv_epilogue_19324 s0 sm
        (P_rest ∗ resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
         memRegion selfA chunkedStatesSize ∗ A.pool)
        hsp0_align hpcm hrunm hsp_m htr_m)
      (fun sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
        ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

theorem writebackWords63_ek_noop (s1 s2 s3 : State) (sp : SendEkSpills) (w : Words66)
    (h1_x3 : s1.readReg64 .x3 = w.b0.w3) (h1_x4 : s1.readReg64 .x4 = w.b1.w5) (h1_x5 : s1.readReg64 .x5 = w.b4.w4)
    (h1_x6 : s1.readReg64 .x6 = w.b4.w0) (h1_x7 : s1.readReg64 .x7 = w.b3.w1) (h1_x10 : s1.readReg64 .x10 = w.b2.w5)
    (h1_x11 : s1.readReg64 .x11 = w.b4.w1) (h1_x12 : s1.readReg64 .x12 = w.b1.w8) (h1_x13 : s1.readReg64 .x13 = w.b4.w3)
    (h1_x14 : s1.readReg64 .x14 = w.b3.w9) (h1_x15 : s1.readReg64 .x15 = w.b3.w5) (h1_x17 : s1.readReg64 .x17 = w.b1.w3)
    (h1_x18 : s1.readReg64 .x18 = w.b2.w7) (h1_x20 : s1.readReg64 .x20 = w.b1.w6) (h1_x21 : s1.readReg64 .x21 = w.b0.w7)
    (h1_x22 : s1.readReg64 .x22 = w.b0.w4) (h1_x23 : s1.readReg64 .x23 = w.b5.w2) (h1_x26 : s1.readReg64 .x26 = w.b1.w0)
    (h1_x27 : s1.readReg64 .x27 = w.b1.w2) (h1_x30 : s1.readReg64 .x30 = w.b2.w3)
    (h2_x0 : s2.readReg64 .x0 = s1.readReg64 .x14) (h2_x1 : s2.readReg64 .x1 = (ekLoadSpills sp w).b0.w7)
    (h2_x2 : s2.readReg64 .x2 = (ekLoadSpills sp w).b5.w8) (h2_x3 : s2.readReg64 .x3 = (ekLoadSpills sp w).b1.w1)
    (h2_x4 : s2.readReg64 .x4 = (ekLoadSpills sp w).b2.w2) (h2_x6 : s2.readReg64 .x6 = s1.readReg64 .x6)
    (h2_x7 : s2.readReg64 .x7 = (ekLoadSpills sp w).b0.w7) (h2_x9 : s2.readReg64 .x9 = (ekLoadSpills sp w).b5.w4)
    (h2_x10 : s2.readReg64 .x10 = s1.readReg64 .x15) (h2_x12 : s2.readReg64 .x12 = (ekLoadSpills sp w).b0.w9)
    (h2_x13 : s2.readReg64 .x13 = (ekLoadSpills sp w).w60) (h2_x16 : s2.readReg64 .x16 = s1.readReg64 .x11)
    (h2_x17 : s2.readReg64 .x17 = (ekLoadSpills sp w).b1.w4) (h2_x20 : s2.readReg64 .x20 = (ekLoadSpills sp w).b5.w9)
    (h2_x23 : s2.readReg64 .x23 = s1.readReg64 .x23) (h2_x25 : s2.readReg64 .x25 = (ekLoadSpills sp w).b0.w4)
    (h2_x26 : s2.readReg64 .x26 = (ekLoadSpills sp w).b2.w0) (h2_x27 : s2.readReg64 .x27 = (ekLoadSpills sp w).b1.w0)
    (h2_x30 : s2.readReg64 .x30 = (ekLoadSpills sp w).b0.w8)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x0) (h3_x1 : s3.readReg64 .x1 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w6)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x27) (h3_x3 : s3.readReg64 .x3 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b0.w3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w6)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x6) (h3_x7 : s3.readReg64 .x7 = s2.readReg64 .x7)
    (h3_x8 : s3.readReg64 .x8 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w5)
    (h3_x9 : s3.readReg64 .x9 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = s2.readReg64 .x10) (h3_x11 : s3.readReg64 .x11 = s2.readReg64 .x30)
    (h3_x12 : s3.readReg64 .x12 = s2.readReg64 .x12) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x23)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x17) (h3_x15 : s3.readReg64 .x15 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x3) (h3_x17 : s3.readReg64 .x17 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w4)
    (h3_x20 : s3.readReg64 .x20 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w7)
    (h3_x21 : s3.readReg64 .x21 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b2.w1)
    (h3_x23 : s3.readReg64 .x23 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b0.w2)
    (h3_x25 : s3.readReg64 .x25 = s2.readReg64 .x25) (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x26)
    (h3_x27 : s3.readReg64 .x27 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w9)
    (h3_x28 : s3.readReg64 .x28 = (ekSpills10136 s1 (ekLoadSpills sp w) w.q60).b1.w5)
    (h3_x30 : s3.readReg64 .x30 = s2.readReg64 .x16) :
    writebackWords63 s3 (ekSpills10276 s2 (ekSpills10136 s1 (ekLoadSpills sp w) w.q60)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5, q60 := w.q60, w62 := w.w62 } := by
  dsimp only [writebackWords63, ekSpills10276, ekSpills10136, ekLoadSpills]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9, h3_x10, h3_x11, h3_x12, h3_x13,
    h3_x14, h3_x15, h3_x16, h3_x17, h3_x20, h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30,
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x6, h2_x7, h2_x9, h2_x10, h2_x12, h2_x13, h2_x16, h2_x17, h2_x20, h2_x23,
    h2_x25, h2_x26, h2_x27, h2_x30, ekSpills10136, ekLoadSpills, h1_x3, h1_x4, h1_x5, h1_x6, h1_x7, h1_x10, h1_x11,
    h1_x12, h1_x13, h1_x14, h1_x15, h1_x17, h1_x18, h1_x20, h1_x21, h1_x22, h1_x23, h1_x26, h1_x27, h1_x30]

theorem writebackWords63_ek_ack (s2 s3 : State) (sp : SendEkSpills) (w : Words57)
    (h2_x0 : s2.readReg64 .x0 = w.b3.w9) (h2_x2 : s2.readReg64 .x2 = w.b4.w6) (h2_x3 : s2.readReg64 .x3 = w.w55)
    (h2_x4 : s2.readReg64 .x4 = w.b4.w9) (h2_x6 : s2.readReg64 .x6 = w.b4.w0) (h2_x7 : s2.readReg64 .x7 = w.b3.w8)
    (h2_x9 : s2.readReg64 .x9 = w.b1.w7) (h2_x10 : s2.readReg64 .x10 = w.b3.w5) (h2_x12 : s2.readReg64 .x12 = w.b3.w3)
    (h2_x13 : s2.readReg64 .x13 = w.w56) (h2_x16 : s2.readReg64 .x16 = w.b4.w1) (h2_x17 : s2.readReg64 .x17 = w.w53)
    (h2_x20 : s2.readReg64 .x20 = w.w54) (h2_x23 : s2.readReg64 .x23 = w.w52) (h2_x25 : s2.readReg64 .x25 = w.b3.w2)
    (h2_x26 : s2.readReg64 .x26 = w.b4.w7) (h2_x30 : s2.readReg64 .x30 = w.b3.w4)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x0) (h3_x1 : s3.readReg64 .x1 = (ekSpills9788 sp w).b1.w6)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x27) (h3_x3 : s3.readReg64 .x3 = (ekSpills9788 sp w).b0.w3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = (ekSpills9788 sp w).b2.w6)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x6) (h3_x7 : s3.readReg64 .x7 = s2.readReg64 .x7)
    (h3_x8 : s3.readReg64 .x8 = (ekSpills9788 sp w).b2.w5) (h3_x9 : s3.readReg64 .x9 = (ekSpills9788 sp w).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = s2.readReg64 .x10) (h3_x11 : s3.readReg64 .x11 = s2.readReg64 .x30)
    (h3_x12 : s3.readReg64 .x12 = s2.readReg64 .x12) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x23)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x17) (h3_x15 : s3.readReg64 .x15 = (ekSpills9788 sp w).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x3) (h3_x17 : s3.readReg64 .x17 = (ekSpills9788 sp w).b2.w4)
    (h3_x20 : s3.readReg64 .x20 = (ekSpills9788 sp w).b1.w7) (h3_x21 : s3.readReg64 .x21 = (ekSpills9788 sp w).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = (ekSpills9788 sp w).b2.w1) (h3_x23 : s3.readReg64 .x23 = (ekSpills9788 sp w).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = (ekSpills9788 sp w).b0.w2) (h3_x25 : s3.readReg64 .x25 = s2.readReg64 .x25)
    (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x26) (h3_x27 : s3.readReg64 .x27 = (ekSpills9788 sp w).b1.w9)
    (h3_x28 : s3.readReg64 .x28 = (ekSpills9788 sp w).b1.w5) (h3_x30 : s3.readReg64 .x30 = s2.readReg64 .x16) :
    writebackWords63 s3 (ekSpills10276 s2 (ekSpills9788 sp w)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, s2.readReg64 .x27, sp.b3.w0, sp.b1.w7⟩
        q60 := sp.q3c0, w62 := sp.b3.w1 } := by
  dsimp only [writebackWords63, ekSpills10276, ekSpills9788]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9, h3_x10, h3_x11, h3_x12, h3_x13,
    h3_x14, h3_x15, h3_x16, h3_x17, h3_x20, h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30,
    ekSpills9788, h2_x0, h2_x2, h2_x3, h2_x4, h2_x6, h2_x7, h2_x9, h2_x10, h2_x12, h2_x13, h2_x16, h2_x17, h2_x20,
    h2_x23, h2_x25, h2_x26, h2_x30]

structure EkRecvMode (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (ext : String → Option (State → State)) where
  Inv : State → Prop
  P_stk : BitVec 64 → SepProp
  specOut : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F) →
    Message spqrPolyApi → Spec (BitVec 64 × BitVec 64 × BitVec 64)
  seq : ∀ {mid target : BitVec 64} {s : State} {P P_mid : SepProp} {Q : State → Prop}
      {post : State → SepProp → Prop},
    Inv s → SepWP (tripleRatchetProgAtExt b ext) mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) →
    (∀ sm, sm.pc = mid → sm.status = .Running → Inv sm → Q sm →
      SepWP (tripleRatchetProgAtExt b ext) target sm P_mid post) →
    SepWP (tripleRatchetProgAtExt b ext) target s P post
  seq_p : ∀ {mid ret : BitVec 64} {s : State} {P P_mid : SepProp} {Q : State → Prop}
      {Q_ok Q_pan : State → SepProp → Prop},
    Inv s → SepWP (tripleRatchetProgAtExt b ext) mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm) →
    (∀ sm, sm.pc = mid → sm.status = .Running → Inv sm → Q sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm P_mid Q_ok Q_pan) →
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q_ok Q_pan
  writeback : ∀ {F_tail : BitVec 64 → SepProp}, Relocatable 376 F_tail →
    ∀ (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp),
    Inv s → s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64 →
    s.status = .Running → s.sp = s0.sp - 4240#64 → s0.spAligned = true →
    s.readReg64 .x19 = outA → TraceCalleeSaved s s0 →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (P_rest ∗ memRegion outA v1RecvSize ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
  exit_p : ∀ (s0 s : State) (outA selfA msgA : BitVec 64)
      (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
      (msg : Message spqrPolyApi) (P R : SepProp),
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P
      (fun sf Pf =>
        (Pf ⊢ P_stk s0.sp ∗ resultV1RecvAt A (F := F) outA ((States.ekReceivedCt1Sampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (specOut st msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (specOut st msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)
  call_ack : ∀ (s0 s : State) (outA selfA msgA : BitVec 64)
      (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
      (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
      (msg : Message spqrPolyApi) (Frame R : SepProp),
    b &&& 0xfff#64 = 0#64 → Inv s → st.recv_ct1_ack K st.uc.epoch = .ok outSt →
    ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName →
    s.status = .Running → s.sp = s0.sp - 4240#64 →
    s.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 →
    s.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 →
    s.readReg64 .x2 = st.uc.epoch → s.readReg64 .x19 = outA →
    s.readReg64 Reg.lr = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9788#64 →
    TraceCalleeSaved s s0 →
    (∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9788#64 →
      sf.status = .Running → sf.sp = s0.sp - 4240#64 →
      sf.readReg64 .x19 = outA → TraceCalleeSaved sf s0 → Inv sf →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) sf
        ((chunkedCt2SampledAt A ((s0.sp - 4240#64) + 976#64) outSt ∗
          memRegion ((s0.sp - 4240#64) + 1856#64) chunkedEkReceivedCt1SampledSize ∗
          unchunkedSendCt2RoAt b ∗ A.pool ∗ P_stk s0.sp ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX) ∗ Frame)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (specOut st msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (specOut st msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)) →
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s
      ((memRegion ((s0.sp - 4240#64) + 976#64) chunkedCt2SampledSize ∗
        chunkedEkReceivedCt1SampledAt A ((s0.sp - 4240#64) + 1856#64) st ∗
        unchunkedSendCt2RoAt b ∗ A.pool ∗ P_stk s0.sp ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX) ∗ Frame)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (specOut st msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (specOut st msg).onPanic (outA, selfA, msgA) s0 sf ∗ R)

private theorem ek_noop_10136_ret_gen
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} (M : EkRecvMode A F K b ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words66) (sp : SendEkSpills) (P_rest : SepProp) (hinv1 : M.Inv s1) (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10136#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64) (hx1 : s1.readReg64 .x1 = selfA)
    (hx3 : s1.readReg64 .x3 = w.b0.w3) (hx4 : s1.readReg64 .x4 = w.b1.w5) (hx5 : s1.readReg64 .x5 = w.b4.w4)
    (hx6 : s1.readReg64 .x6 = w.b4.w0) (hx7 : s1.readReg64 .x7 = w.b3.w1) (hx10 : s1.readReg64 .x10 = w.b2.w5)
    (hx11 : s1.readReg64 .x11 = w.b4.w1) (hx12 : s1.readReg64 .x12 = w.b1.w8) (hx13 : s1.readReg64 .x13 = w.b4.w3)
    (hx14 : s1.readReg64 .x14 = w.b3.w9) (hx15 : s1.readReg64 .x15 = w.b3.w5) (hx17 : s1.readReg64 .x17 = w.b1.w3)
    (hx18 : s1.readReg64 .x18 = w.b2.w7) (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = w.b1.w6)
    (hx21 : s1.readReg64 .x21 = w.b0.w7) (hx22 : s1.readReg64 .x22 = w.b0.w4) (hx23 : s1.readReg64 .x23 = w.b5.w2)
    (hx26 : s1.readReg64 .x26 = w.b1.w0) (hx27 : s1.readReg64 .x27 = w.b1.w2) (hx30 : s1.readReg64 .x30 = w.b2.w3)
    (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
        memRegion (selfA + 536#64) 392 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) (ekLoadSpills sp w) ∗
        memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (((s0.sp - 4240#64) + 2752#64) ↦₁₂₈ w.q60) ∗ (((s0.sp - 4240#64) + 3856#64) ↦₁₂₈ w.q63) ∗
        ekUnusedRestAt (s0.sp - 4240#64) ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekReceivedCt1Sampled st }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (memRegion_576_376_split_ekTail fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i q576_old w592_old
  set sp1 := ekSpills10136 s1 (ekLoadSpills sp w) w.q60
  refine M.seq hinv1 (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10276#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = s1.readReg64 .x14 ∧
      s2.readReg64 .x1 = (ekLoadSpills sp w).b0.w7 ∧ s2.readReg64 .x2 = (ekLoadSpills sp w).b5.w8 ∧
      s2.readReg64 .x3 = (ekLoadSpills sp w).b1.w1 ∧ s2.readReg64 .x4 = (ekLoadSpills sp w).b2.w2 ∧
      s2.readReg64 .x6 = s1.readReg64 .x6 ∧ s2.readReg64 .x7 = (ekLoadSpills sp w).b0.w7 ∧
      s2.readReg64 .x9 = (ekLoadSpills sp w).b5.w4 ∧ s2.readReg64 .x10 = s1.readReg64 .x15 ∧
      s2.readReg64 .x12 = (ekLoadSpills sp w).b0.w9 ∧ s2.readReg64 .x13 = (ekLoadSpills sp w).w60 ∧
      s2.readReg64 .x16 = s1.readReg64 .x11 ∧ s2.readReg64 .x17 = (ekLoadSpills sp w).b1.w4 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x20 = (ekLoadSpills sp w).b5.w9 ∧
      s2.readReg64 .x23 = s1.readReg64 .x23 ∧ s2.readReg64 .x25 = (ekLoadSpills sp w).b0.w4 ∧
      s2.readReg64 .x26 = (ekLoadSpills sp w).b2.w0 ∧ s2.readReg64 .x27 = (ekLoadSpills sp w).b1.w0 ∧
      s2.readReg64 .x30 = (ekLoadSpills sp w).b0.w8 ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep := ek_step_10136_10276 s1 fsp selfA w592_old q576_old w (ekLoadSpills sp w)
      (P_rest ∗ memRegion outA v1RecvSize ∗ (selfA ↦₆₄ 10#64) ∗
       words10At (selfA + 8#64) w.b0 ∗ words10At (selfA + 88#64) w.b1 ∗
       words10At (selfA + 168#64) w.b2 ∗ words10At (selfA + 248#64) w.b3 ∗
       words10At (selfA + 328#64) w.b4 ∗ words10At (selfA + 408#64) w.b5 ∗
       ((selfA + 504#64) ↦₆₄ w.w62) ∗ memRegion (selfA + 536#64) 392 ∗
       relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
       stackAt fsp statesRecvCalleeStackX ∗
       ((fsp + 496#64) ↦₆₄ (ekLoadSpills sp w).w61) ∗ ((fsp + 504#64) ↦₆₄ (ekLoadSpills sp w).w62) ∗
       ((fsp + 512#64) ↦₁₂₈ (ekLoadSpills sp w).q200) ∗ ((fsp + 528#64) ↦₁₂₈ (ekLoadSpills sp w).q210) ∗
       ((fsp + 544#64) ↦₁₂₈ (ekLoadSpills sp w).q220) ∗ ((fsp + 560#64) ↦₆₄ (ekLoadSpills sp w).w230) ∗
       memRegion (fsp + 600#64) 352 ∗ memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
       ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
       ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp hx1
    refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep ?_)
    · dsimp only [words66At, sendEkSpillsAt]; simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl
    · intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
        h2_13, h2_16, h2_17, h2_19, h2_20, h2_23, h2_25, h2_26, h2_27, _, h2_30, htr2⟩
      refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
        h2_13, h2_16, h2_17, h2_19.trans hx19, h2_20, h2_23, h2_25, h2_26, h2_27, h2_30, htr2.trans htr⟩
      have hself := selfA_ekReceivedCt1Sampled_entails_memRegion selfA w
      have hunused := ekUnusedRest_entails_sendEkUnusedAt fsp w.q60 w.q63
      refine Entails.trans (Entails.of_eq (show _ =
        (((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
         (((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ ekUnusedRestAt fsp)) ∗
        (P_rest ∗ memRegion outA v1RecvSize ∗
         relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
         ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
         memRegion (fsp + 1856#64) 880 ∗ statesRecvSavedCells s0) by
          dsimp only [words66At, sendEkSpillsAt, sp1, ekSpills10136, ekTail376]
          simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]; sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left (sepConj_mono hself hunused)) (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_0, h2_1, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
      h2_13, h2_16, h2_17, h2_19, h2_20, h2_23, h2_25, h2_26, h2_27, h2_30, htr2⟩
    set sp2 := ekSpills10276 s2 sp1
    refine M.seq hinv2 (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        ekTail376 w.q63 w.w65 (fsp + 576#64) ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
            q60 := w.q60, w62 := w.w62 } ∧ TraceCalleeSaved s3 s0) ?_ ?_
    · have hstep2 := ek_step_10276_18996 s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
         stackAt fsp statesRecvCalleeStackX ∗
         words10At (fsp + 248#64) sp1.b3 ∗ words10At (fsp + 328#64) sp1.b4 ∗
         ((fsp + 496#64) ↦₆₄ sp1.w61) ∗ ((fsp + 504#64) ↦₆₄ sp1.w62) ∗
         ((fsp + 512#64) ↦₁₂₈ sp1.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp1.q210) ∗
         ((fsp + 544#64) ↦₁₂₈ sp1.q220) ∗ ((fsp + 560#64) ↦₆₄ sp1.w230) ∗
         ((fsp + 960#64) ↦₁₂₈ sp1.q3c0) ∗ ekTail376 w.q63 w.w65 (fsp + 576#64) ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep2 ?_)
      · dsimp only [sendEkSpillsAt]; sep_ac_rfl
      · intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9,
          h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19, h3_20, h3_21, h3_22,
          h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
        have hwb := writebackWords63_ek_noop s1 s2 s3 sp w
          hx3 hx4 hx5 hx6 hx7 hx10 hx11 hx12 hx13 hx14 hx15 hx17 hx18 hx20 hx21 hx22 hx23 hx26 hx27 hx30
          h2_0 h2_1 h2_2 h2_3 h2_4 h2_6 h2_7 h2_9 h2_10 h2_12 h2_13 h2_16 h2_17 h2_20 h2_23 h2_25 h2_26 h2_27 h2_30
          h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12 h3_13 h3_14 h3_15 h3_16 h3_17 h3_20
          h3_21 h3_22 h3_23 h3_24 h3_25 h3_26 h3_27 h3_28 h3_30
        refine ⟨Entails.trans hPm (Entails.of_eq ?_), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
        dsimp only [sendEkSpillsAt, sp2, ekSpills10276]; sep_ac_rfl
    · intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := M.writeback (relocatable_ekTail376 w.q63 w.w65) s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)))
        hinv3 hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 10#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ek_noop_out_entails_resultV1RecvAt A (F := F) outA st w (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 10#64) ∗
         words63At (outA + 8#64)
           { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
             q60 := w.q60, w62 := w.w62 } ∗
         ekTail376 w.q63 w.w65 (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

theorem ek_step_9784_call
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp msg_ep : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9784#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 976#64) (hx1 : s.readReg64 .x1 = fsp + 1856#64)
    (hx2 : s.readReg64 .x2 = msg_ep) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName) s Frame
      (fun sm Pm =>
        (Pm ⊢ Frame) ∧ sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 976#64 ∧
        sm.readReg64 .x1 = fsp + 1856#64 ∧ sm.readReg64 .x2 = msg_ep ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9788#64 ∧
        CalleeSavedPreserved s sm ∧ TraceCalleeSaved sm s) := by
  subst hsp hx2
  states_recv_fetches_range b (Rust.withPanics ext) 9784 4
  have hfn : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      ekReceivedCt1SampledRecvCt1AckName =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr statesRecvName + 36008#64 := by
    dsimp only [statesRecvName, ekReceivedCt1SampledRecvCt1AckName]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
        libsignalSessionCode_fnOff_0x5005c, libsignalSessionCode_fnOff_0x58d04]; bv_omega
  dsimp only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpc hfn ⊢
  rw [hfn]; dsimp only [statesRecvName] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; wp_steps; wp_done

theorem memRegion_1856_880_entails_words66 (fsp : BitVec 64) :
    memRegion (fsp + 1856#64) 880 ⊢
      ∃∗ u740 : Words66, words66At (fsp + 1856#64) u740 ∗ memRegion (fsp + 2384#64) 352 := by
  rw [memRegion_880_split_528_352 fsp]
  refine Entails.trans (sepConj_mono_left (memRegion_528_entails_words66At (fsp + 1856#64))) ?_
  rw [sepExists_sepConj_left]; exact Entails.refl _

theorem ek_step_9344_to_call_entry
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (outA selfA : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (w : Words66) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9344#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx3 : s1.readReg64 .x3 = w.b0.w3) (hx4 : s1.readReg64 .x4 = w.b1.w5) (hx5 : s1.readReg64 .x5 = w.b4.w4)
    (hx6 : s1.readReg64 .x6 = w.b4.w0) (hx7 : s1.readReg64 .x7 = w.b3.w1) (hx10 : s1.readReg64 .x10 = w.b2.w5)
    (hx11 : s1.readReg64 .x11 = w.b4.w1) (hx12 : s1.readReg64 .x12 = w.b1.w8) (hx13 : s1.readReg64 .x13 = w.b4.w3)
    (hx14 : s1.readReg64 .x14 = w.b3.w9) (hx15 : s1.readReg64 .x15 = w.b3.w5) (hx17 : s1.readReg64 .x17 = w.b1.w3)
    (hx18 : s1.readReg64 .x18 = w.b2.w7) (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = w.b1.w6)
    (hx21 : s1.readReg64 .x21 = w.b0.w7) (hx22 : s1.readReg64 .x22 = w.b0.w4) (hx23 : s1.readReg64 .x23 = w.b5.w2)
    (hx25 : s1.readReg64 .x25 = st.uc.epoch) (hx26 : s1.readReg64 .x26 = w.b1.w0) (hx27 : s1.readReg64 .x27 = w.b1.w2)
    (hx28 : s1.readReg64 .x28 = w.w65) (hx30 : s1.readReg64 .x30 = w.b2.w3) (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName) s1
      ((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
        memRegion (selfA + 536#64) 392 ∗ sendEkSpillsAt (s0.sp - 4240#64) (ekLoadSpills sp w) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (((s0.sp - 4240#64) + 2752#64) ↦₁₂₈ w.q60) ∗ (((s0.sp - 4240#64) + 3856#64) ↦₁₂₈ w.q63) ∗
        ekUnusedRestAt (s0.sp - 4240#64) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion selfA chunkedStatesSize ∗
          memRegion ((s0.sp - 4240#64) + 976#64) chunkedCt2SampledSize ∗
          memRegion ((s0.sp - 4240#64) + 1432#64) 424 ∗
          chunkedEkReceivedCt1SampledAt A ((s0.sp - 4240#64) + 1856#64) st ∗
          memRegion ((s0.sp - 4240#64) + 2384#64) 352 ∗
          sendEkSpillsAt (s0.sp - 4240#64) (ekLoadSpills sp w) ∗
          sendEkUnusedAt (s0.sp - 4240#64) ∗ Frame) ∧
        sm.sp = s0.sp - 4240#64 ∧ sm.readReg64 .x0 = (s0.sp - 4240#64) + 976#64 ∧
        sm.readReg64 .x1 = (s0.sp - 4240#64) + 1856#64 ∧ sm.readReg64 .x2 = st.uc.epoch ∧
        sm.readReg64 .x19 = outA ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9788#64 ∧
        TraceCalleeSaved sm s0) := by
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (memRegion_1856_880_entails_words66 fsp) (by sep_focus) ?_
  wp_pull_exists; rename_i u740
  refine seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9784#64)
    (P_mid := memRegion selfA chunkedStatesSize ∗ memRegion (fsp + 976#64) chunkedCt2SampledSize ∗
      memRegion (fsp + 1432#64) 424 ∗ chunkedEkReceivedCt1SampledAt A (fsp + 1856#64) st ∗
      memRegion (fsp + 2384#64) 352 ∗ sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
      sendEkUnusedAt fsp ∗ Frame)
    (Q := fun s2 => s2.sp = fsp ∧ s2.readReg64 .x0 = fsp + 976#64 ∧
      s2.readReg64 .x1 = fsp + 1856#64 ∧ s2.readReg64 .x2 = st.uc.epoch ∧
      s2.readReg64 .x19 = outA ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep := ek_step_9344_9784 s1 fsp st.uc.epoch w u740 sp
      ((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗
       relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
       memRegion (selfA + 536#64) 392 ∗ memRegion (fsp + 976#64) 880 ∗
       memRegion (fsp + 2384#64) 352 ∗ ekUnusedRestAt fsp ∗ Frame)
      hfsp_align hpc hrun hsp
      hx3 hx4 hx5 hx6 hx7 hx10 hx11 hx12 hx13 hx14 hx15 hx17 hx18 hx20 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx30
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h0_2, h1_2, h2_2, h19_2, _, htr2⟩
    refine ⟨Entails.trans hPm ?_, hsp2, h0_2, h1_2, h2_2, h19_2.trans hx19, htr2.trans htr⟩
    have hself := selfA_ekReceivedCt1Sampled_entails_memRegion selfA w
    have hrec := recompose66 (F_pred := fun dst => chunkedEkReceivedCt1SampledAt A dst st) (fsp + 1856#64) w
    have hunused := ekUnusedRest_entails_sendEkUnusedAt fsp w.q60 w.q63
    unfold chunkedCt2SampledSize; rw [memRegion_880_split_456_424 fsp]
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392) ∗
      (words66At (fsp + 1856#64) w ∗
       relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
      (((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ ekUnusedRestAt fsp) ∗
      (memRegion (fsp + 976#64) 456 ∗ memRegion (fsp + 1432#64) 424 ∗
       memRegion (fsp + 2384#64) 352 ∗ sendEkSpillsAt fsp (ekLoadSpills sp w) ∗ Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono hself (sepConj_mono hrec (sepConj_mono_left hunused))) (Entails.of_eq (by ac_rfl))
  · intro s2 hpc2 hrun2 ⟨hsp2, h0_2, h1_2, h2_2, h19_2, htr2⟩
    have hcall := ek_step_9784_call s2 fsp st.uc.epoch
      (memRegion selfA chunkedStatesSize ∗ memRegion (fsp + 976#64) chunkedCt2SampledSize ∗
       memRegion (fsp + 1432#64) 424 ∗ chunkedEkReceivedCt1SampledAt A (fsp + 1856#64) st ∗
       memRegion (fsp + 2384#64) 352 ∗ sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
       sendEkUnusedAt fsp ∗ Frame)
      hpc2 hrun2 hsp2 h0_2 h1_2 h2_2
    refine SepWP.mono hcall ?_
    intro sm Pm _ _ ⟨hPm, hsp_m, h0_m, h1_m, h2_m, h30_m, hcs_m, htr_m⟩
    exact ⟨hPm, hsp_m, h0_m, h1_m, h2_m, hcs_m.1.trans h19_2, h30_m, htr_m.trans htr2⟩

private theorem ek_ack_9788_ret_gen
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} (M : EkRecvMode A F K b ext)
    (s0 s1 : State) (outA selfA : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (sp : SendEkSpills) (P_rest : SepProp)
    (hinv1 : M.Inv s1) (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9788#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = outA) (htr : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
        chunkedCt2SampledAt A ((s0.sp - 4240#64) + 976#64) outSt ∗
        memRegion ((s0.sp - 4240#64) + 1432#64) 424 ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗ memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ P_rest ∗ resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct2Sampled outSt }) ∗
          memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine SepWP.fold (chunkedCt2SampledAt_extract57 A (fsp + 976#64) outSt) (by sep_focus) ?_
  wp_pull_exists; rename_i w57
  set sp1 := ekSpills9788 sp w57
  refine M.seq hinv1 (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 10276#64)
    (P_mid := P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57)) ∗
      stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
      memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
      memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
    (Q := fun s2 =>
      s2.sp = fsp ∧ s2.readReg64 .x0 = w57.b3.w9 ∧ s2.readReg64 .x2 = w57.b4.w6 ∧
      s2.readReg64 .x3 = w57.w55 ∧ s2.readReg64 .x4 = w57.b4.w9 ∧
      s2.readReg64 .x6 = w57.b4.w0 ∧ s2.readReg64 .x7 = w57.b3.w8 ∧
      s2.readReg64 .x9 = w57.b1.w7 ∧ s2.readReg64 .x10 = w57.b3.w5 ∧
      s2.readReg64 .x12 = w57.b3.w3 ∧ s2.readReg64 .x13 = w57.w56 ∧
      s2.readReg64 .x16 = w57.b4.w1 ∧ s2.readReg64 .x17 = w57.w53 ∧
      s2.readReg64 .x19 = outA ∧ s2.readReg64 .x20 = w57.w54 ∧
      s2.readReg64 .x23 = w57.w52 ∧ s2.readReg64 .x25 = w57.b3.w2 ∧
      s2.readReg64 .x26 = w57.b4.w7 ∧ s2.readReg64 .x27 = s1.readReg64 .x27 ∧
      s2.readReg64 .x30 = w57.b3.w4 ∧ TraceCalleeSaved s2 s0) ?_ ?_
  · have hstep := ek_step_9788_10276 s1 fsp w57 sp
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57)) ∗
       memRegion (fsp + 1432#64) 424 ∗ stackAt fsp statesRecvCalleeStackX ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1856#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp
    refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
      h2_13, h2_16, h2_17, h2_19, h2_20, h2_23, h2_25, h2_26, h2_27, _, h2_30, htr2⟩
    refine ⟨Entails.trans hPm ?_, hsp2, h2_0, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
      h2_13, h2_16, h2_17, h2_19.trans hx19, h2_20, h2_23, h2_25, h2_26, h2_27, h2_30, htr2.trans htr⟩
    have h880 := words57At_424_entails_memRegion_880 fsp w57
    refine Entails.trans (Entails.of_eq (show _ =
      (words57At (fsp + 976#64) w57 ∗ memRegion (fsp + 1432#64) 424) ∗
      (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57)) ∗
       stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp1 ∗
       memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1856#64) 880 ∗
       sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h880) (Entails.of_eq (by sep_ac_rfl))
  · intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h2_0, h2_2, h2_3, h2_4, h2_6, h2_7, h2_9, h2_10, h2_12,
      h2_13, h2_16, h2_17, h2_19, h2_20, h2_23, h2_25, h2_26, h2_27, h2_30, htr2⟩
    set sp2 := ekSpills10276 s2 sp1
    refine M.seq hinv2 (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
      (P_mid := (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57))) ∗
        memRegion outA v1RecvSize ∗ stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp sp2 ∗
        memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 880 ∗
        memRegion (fsp + 1856#64) 880 ∗ sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
      (Q := fun s3 => s3.sp = fsp ∧ s3.readReg64 .x19 = outA ∧
        writebackWords63 s3 sp2 =
          { b0 := w57.b0, b1 := w57.b1, b2 := w57.b2, b3 := w57.b3, b4 := w57.b4
            b5 := ⟨w57.w50, w57.w51, w57.w52, w57.w53, w57.w54, w57.w55, w57.w56,
                   s2.readReg64 .x27, sp.b3.w0, sp.b1.w7⟩
            q60 := sp.q3c0, w62 := sp.b3.w1 } ∧ TraceCalleeSaved s3 s0) ?_ ?_
    · have hstep2 := ek_step_10276_18996 s2 fsp sp1
        (P_rest ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57)) ∗
         stackAt fsp statesRecvCalleeStackX ∗
         words10At (fsp + 248#64) sp1.b3 ∗ words10At (fsp + 328#64) sp1.b4 ∗
         ((fsp + 496#64) ↦₆₄ sp1.w61) ∗ ((fsp + 504#64) ↦₆₄ sp1.w62) ∗
         ((fsp + 512#64) ↦₁₂₈ sp1.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp1.q210) ∗
         ((fsp + 544#64) ↦₁₂₈ sp1.q220) ∗ ((fsp + 560#64) ↦₆₄ sp1.w230) ∗
         ((fsp + 960#64) ↦₁₂₈ sp1.q3c0) ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         sendEkUnusedAt fsp ∗ statesRecvSavedCells s0)
        hfsp_align hpc2 hrun2 hsp2
      refine SepWP.weaken_pre (Entails.of_eq ?_) (SepWP.mono hstep2 ?_)
      · dsimp only [sendEkSpillsAt]; sep_ac_rfl
      · intro s3 Pm _ _ ⟨hPm, hsp3, h3_0, h3_1, h3_2, h3_3, h3_4, h3_5, h3_6, h3_7, h3_8, h3_9,
          h3_10, h3_11, h3_12, h3_13, h3_14, h3_15, h3_16, h3_17, h3_19, h3_20, h3_21, h3_22,
          h3_23, h3_24, h3_25, h3_26, h3_27, h3_28, _, h3_30, htr3⟩
        have hwb := writebackWords63_ek_ack s2 s3 sp w57
          h2_0 h2_2 h2_3 h2_4 h2_6 h2_7 h2_9 h2_10 h2_12 h2_13 h2_16 h2_17 h2_20 h2_23 h2_25 h2_26 h2_30
          h3_0 h3_1 h3_2 h3_3 h3_4 h3_5 h3_6 h3_7 h3_8 h3_9 h3_10 h3_11 h3_12 h3_13 h3_14 h3_15 h3_16 h3_17 h3_20
          h3_21 h3_22 h3_23 h3_24 h3_25 h3_26 h3_27 h3_28 h3_30
        refine ⟨Entails.trans hPm (Entails.of_eq ?_), hsp3, h3_19.trans h2_19, hwb, htr3.trans htr2⟩
        dsimp only [sendEkSpillsAt, sp2, ekSpills10276]; sep_ac_rfl
    · intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_19, hwb, htr3⟩
      have hwrite := M.writeback (Relocatable.of_memRegion 376) s0 s3 outA sp2
        (P_rest ∗ memRegion selfA chunkedStatesSize ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57)))
        hinv3 hpc3 hrun3 hsp3 hsp0_align h3_19 htr3
      refine SepWP.mono hwrite ?_
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      have htag : sp2.b2.w7 = 12#64 := rfl
      have hnone : sp2.b2.w8 = noneCap := rfl
      rw [htag, hnone, hwb]
      have hout := ek_ack_out_entails_resultV1RecvAt A (F := F) outA outSt w57
        (s2.readReg64 .x27) sp.b3.w0 sp.b1.w7 sp.q3c0 sp.b3.w1 (s3.readReg64 .x20) sp2.q200
      refine Entails.trans (Entails.of_eq (show _ =
        P_rest ∗ ((outA ↦₆₄ 12#64) ∗
         words63At (outA + 8#64)
           { b0 := w57.b0, b1 := w57.b1, b2 := w57.b2, b3 := w57.b3, b4 := w57.b4
             b5 := ⟨w57.w50, w57.w51, w57.w52, w57.w53, w57.w54, w57.w55, w57.w56,
                    s2.readReg64 .x27, sp.b3.w0, sp.b1.w7⟩
             q60 := sp.q3c0, w62 := sp.b3.w1 } ∗
         memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ∗
         ((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
         ((outA + 944#64) ↦₁₂₈ sp2.q200) ∗
         relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w57))) ∗
        memRegion selfA chunkedStatesSize ∗ stackAt s0.sp statesRecvStackX by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_left hout)

private theorem ek_ack_9344_ok_ret_gen
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} (M : EkRecvMode A F K b ext)
    (hb : b &&& 0xfff#64 = 0#64) (s0 s1 : State) (outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (w : Words66) (sp : SendEkSpills) (R : SepProp)
    (hinv1 : M.Inv s1) (heq : msg.epoch = st.uc.epoch)
    (hack : (match msg.payload with | .ct1Ack true => true | .ekCt1Ack _ => true | _ => false) = true)
    (hok : st.recv_ct1_ack K st.uc.epoch = .ok outSt) (hsp0_align : s0.spAligned = true)
    (hpc : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 9344#64)
    (hrun : s1.status = .Running) (hsp : s1.sp = s0.sp - 4240#64)
    (hx3 : s1.readReg64 .x3 = w.b0.w3) (hx4 : s1.readReg64 .x4 = w.b1.w5) (hx5 : s1.readReg64 .x5 = w.b4.w4)
    (hx6 : s1.readReg64 .x6 = w.b4.w0) (hx7 : s1.readReg64 .x7 = w.b3.w1) (hx10 : s1.readReg64 .x10 = w.b2.w5)
    (hx11 : s1.readReg64 .x11 = w.b4.w1) (hx12 : s1.readReg64 .x12 = w.b1.w8) (hx13 : s1.readReg64 .x13 = w.b4.w3)
    (hx14 : s1.readReg64 .x14 = w.b3.w9) (hx15 : s1.readReg64 .x15 = w.b3.w5) (hx17 : s1.readReg64 .x17 = w.b1.w3)
    (hx18 : s1.readReg64 .x18 = w.b2.w7) (hx19 : s1.readReg64 .x19 = outA) (hx20 : s1.readReg64 .x20 = w.b1.w6)
    (hx21 : s1.readReg64 .x21 = w.b0.w7) (hx22 : s1.readReg64 .x22 = w.b0.w4) (hx23 : s1.readReg64 .x23 = w.b5.w2)
    (hx25 : s1.readReg64 .x25 = st.uc.epoch) (hx26 : s1.readReg64 .x26 = w.b1.w0) (hx27 : s1.readReg64 .x27 = w.b1.w2)
    (hx28 : s1.readReg64 .x28 = w.w65) (hx30 : s1.readReg64 .x30 = w.b2.w3) (htr : TraceCalleeSaved s1 s0) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s1
      ((selfA ↦₆₄ 10#64) ∗ words66At (selfA + 8#64) w ∗
        relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
        memRegion (selfA + 536#64) 392 ∗ sendEkSpillsAt (s0.sp - 4240#64) (ekLoadSpills sp w) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗ memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        (((s0.sp - 4240#64) + 2752#64) ↦₁₂₈ w.q60) ∗ (((s0.sp - 4240#64) + 3856#64) ↦₁₂₈ w.q63) ∗
        ekUnusedRestAt (s0.sp - 4240#64) ∗
        (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗
         A.pool ∗ stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion ((s0.sp - 4240#64) + 576#64) 376 ∗ statesRecvSavedCells s0))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (M.specOut st msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (M.specOut st msg).onPanic (outA, selfA, msgA) s0 sf ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  set fsp := s0.sp - 4240#64
  refine M.seq_p hinv1
    (ek_step_9344_to_call_entry s0 s1 outA selfA st w sp
      (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗ statesRecvSavedCells s0)
      hfsp_align hpc hrun hsp
      hx3 hx4 hx5 hx6 hx7 hx10 hx11 hx12 hx13 hx14 hx15 hx17 hx18 hx19 hx20 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx30 htr)
    ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, h0_2, h1_2, h2_2, h19_2, h30_2, htr2⟩
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion (fsp + 976#64) chunkedCt2SampledSize ∗
     chunkedEkReceivedCt1SampledAt A (fsp + 1856#64) st ∗
     unchunkedSendCt2RoAt b ∗ A.pool ∗ M.P_stk s0.sp ∗ stackAt fsp statesRecvCalleeStackX) ∗
    (messageAt spqrPolyApi msgA msg ∗
     statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
     memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
     memRegion (fsp + 1432#64) 424 ∗ memRegion (fsp + 2384#64) 352 ∗
     sendEkSpillsAt fsp (ekLoadSpills sp w) ∗ memRegion (fsp + 576#64) 376 ∗
     sendEkUnusedAt fsp ∗ statesRecvSavedCells s0) by
      dsimp only [statesRecvRoAt, fsp]; sep_ac_rfl)) ?_
  refine M.call_ack s0 s2 outA selfA msgA st outSt msg _ R
    hb hinv2 hok hfsp_align hpc2 hrun2 hsp2 h0_2 h1_2 h2_2 h19_2 h30_2 htr2 ?_
  intro s3 hpc3 hrun3 hsp3 h19_3 htr3 hinv3
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) ∗
    memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
    chunkedCt2SampledAt A (fsp + 976#64) outSt ∗ memRegion (fsp + 1432#64) 424 ∗
    stackAt fsp statesRecvCalleeStackX ∗ sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
    memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 1856#64) 880 ∗
    sendEkUnusedAt fsp ∗ statesRecvSavedCells s0 by
      dsimp only [statesRecvRoAt, chunkedEkReceivedCt1SampledSize, fsp]
      rw [memRegion_880_split_528_352 (s0.sp - 4240#64)]; sep_ac_rfl)) ?_
  have hexit := ek_ack_9788_ret_gen M s0 s3 outA selfA outSt (ekLoadSpills sp w)
    (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
    hinv3 hsp0_align hpc3 hrun3 hsp3 h19_3 htr3
  have hrecv := states_recv_ekReceivedCt1Sampled_eq_ack_ok K st outSt msg heq hack hok
  refine M.exit_p s0 s3 outA selfA msgA st msg _ R (SepWP.mono hexit ?_)
  intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
  refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
  rw [hrecv]; exact Entails.of_eq (by sep_ac_rfl)

theorem ek_step_3392_3732
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (fsp out st_ptr msg_ptr msg_ep : BitVec 64)
    (w : Words66) (sp : SendEkSpills) (qac0 qf10 : BitVec 128) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 3392#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = st_ptr) (hx19 : s.readReg64 .x19 = out) (hx24 : s.readReg64 .x24 = msg_ptr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 3732#64) s
      (words66At (st_ptr + 8#64) w ∗ (msg_ptr ↦₆₄ msg_ep) ∗
       sendEkSpillsAt fsp sp ∗ ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ words66At (st_ptr + 8#64) w ∗ (msg_ptr ↦₆₄ msg_ep) ∗ sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
          ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = st_ptr + 8#64 ∧ sm.readReg64 .x1 = st_ptr ∧
        sm.readReg64 .x3 = w.b0.w3 ∧ sm.readReg64 .x4 = w.b1.w5 ∧ sm.readReg64 .x5 = w.b4.w4 ∧
        sm.readReg64 .x6 = w.b4.w0 ∧ sm.readReg64 .x7 = w.b3.w1 ∧ sm.readReg64 .x10 = w.b2.w5 ∧
        sm.readReg64 .x11 = w.b4.w1 ∧ sm.readReg64 .x12 = w.b1.w8 ∧ sm.readReg64 .x13 = w.b4.w3 ∧
        sm.readReg64 .x14 = w.b3.w9 ∧ sm.readReg64 .x15 = w.b3.w5 ∧ sm.readReg64 .x17 = w.b1.w3 ∧
        sm.readReg64 .x18 = w.b2.w7 ∧ sm.readReg64 .x19 = out ∧ sm.readReg64 .x20 = w.b1.w6 ∧
        sm.readReg64 .x21 = w.b0.w7 ∧ sm.readReg64 .x22 = w.b0.w4 ∧ sm.readReg64 .x23 = w.b5.w2 ∧
        sm.readReg64 .x24 = msg_ptr ∧ sm.readReg64 .x25 = msg_ep ∧ sm.readReg64 .x26 = w.b1.w0 ∧
        sm.readReg64 .x27 = w.b1.w2 ∧ sm.readReg64 .x28 = w.w65 ∧ sm.readReg64 .x30 = w.b2.w3 ∧
        sm.readReg64 .x8 = BitVec.zeroExtend 64 (ekCmpW8 (subsPState64 msg_ep w.w65)) ∧
        sm.pstate.z = (ekCmpW8 (subsPState64 msg_ep w.w65) == 0#32) ∧ TraceCalleeSaved sm s) := by
  have h1 := ek_step_3392_3560 s fsp out st_ptr msg_ptr msg_ep w sp qac0 qf10
    (words10At (st_ptr + 408#64) w.b5 ∗ ((st_ptr + 504#64) ↦₆₄ w.w62) ∗
     words10At (fsp + 8#64) sp.b0 ∗ ((fsp + 488#64) ↦₆₄ sp.w60) ∗
     ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
     ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗ ((fsp + 560#64) ↦₆₄ sp.w230) ∗
     ((fsp + 960#64) ↦₁₂₈ sp.q3c0) ∗ Frame)
    hfsp_align hpc hrun hsp hx1 hx19 hx24
  refine seq_clean (SepWP.weaken_pre (Entails.of_eq ?_) h1) ?_
  · dsimp only [words66At, sendEkSpillsAt]
    simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
    ac_rfl
  · intro s1 hpc1 hrun1 ⟨hsp1, h1_0, h1_1, h1_3, h1_4, h1_5, h1_6, h1_7, h1_9, h1_10, h1_11,
      h1_12, h1_13, h1_14, h1_17, h1_18, h1_19, h1_20, h1_21, h1_22, h1_24, h1_25, h1_26,
      h1_27, h1_28, _, h1_30, hps1, htr1⟩
    have h2 := ek_step_3560_3732 s1 fsp st_ptr w sp
      (words10At (st_ptr + 8#64) w.b0 ∗ words10At (st_ptr + 88#64) w.b1 ∗
       words10At (st_ptr + 168#64) w.b2 ∗
       ((st_ptr + 488#64) ↦₁₂₈ w.q60) ∗ ((st_ptr + 512#64) ↦₁₂₈ w.q63) ∗ ((st_ptr + 528#64) ↦₆₄ w.w65) ∗
       (msg_ptr ↦₆₄ msg_ep) ∗
       words10At (fsp + 328#64) (ekLoadSpillsA sp w).b4 ∗
       ((fsp + 496#64) ↦₆₄ (ekLoadSpillsA sp w).w61) ∗ ((fsp + 504#64) ↦₆₄ (ekLoadSpillsA sp w).w62) ∗
       ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
       ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗ ((fsp + 560#64) ↦₆₄ sp.w230) ∗
       ((fsp + 960#64) ↦₁₂₈ sp.q3c0) ∗
       ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ Frame)
      hfsp_align hpc1 hrun1 hsp1 h1_0 h1_9 h1_11
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono h2 ?_)
    intro s2 Pm _ _ ⟨hPm, hsp2, h2_0, h2_1, h2_3, h2_4, h2_5, h2_6, h2_7, h2_10, h2_11,
      h2_12, h2_13, h2_14, h2_15, h2_17, h2_18, h2_19, h2_20, h2_21, h2_22, h2_23,
      h2_24, h2_25, h2_26, h2_27, h2_28, _, h2_30, h2_8, h2_z, htr2⟩
    rw [hps1] at h2_8 h2_z
    refine ⟨Entails.trans hPm (Entails.of_eq ?_),
      hsp2, h2_0, h2_1.trans h1_1, h2_3.trans h1_3, h2_4.trans h1_4, h2_5.trans h1_5,
      h2_6.trans h1_6, h2_7.trans h1_7, h2_10.trans h1_10, h2_11, h2_12.trans h1_12,
      h2_13.trans h1_13, h2_14.trans h1_14, h2_15, h2_17.trans h1_17, h2_18.trans h1_18,
      h2_19.trans h1_19, h2_20.trans h1_20, h2_21.trans h1_21, h2_22.trans h1_22, h2_23,
      h2_24.trans h1_24, h2_25.trans h1_25, h2_26.trans h1_26, h2_27.trans h1_27,
      h2_28.trans h1_28, h2_30.trans h1_30, h2_8, h2_z, htr2.trans htr1⟩
    dsimp only [words66At, sendEkSpillsAt, ekLoadSpillsA, ekLoadSpills]
    simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]
    ac_rfl

theorem sepWPp_intro_ex {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q Q_panic : State → SepProp → Prop} (hrun : s.status = .Running)
    (h : ∀ x, SepWPp prog target_pc s (P x) Q Q_panic) :
    SepWPp prog target_pc s (∃∗ x, P x) Q Q_panic := by
  apply SepWPp.of_sepWP
  rw [← emp_sepConj (∃∗ x, P x), sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left
  intro x; rw [emp_sepConj]
  exact SepWP.done rfl hrun (h x)

theorem states_recv_ekReceivedCt1Sampled_sepWPp_gen
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {ext : String → Option (State → State)} (M : EkRecvMode A F K b ext)
    (hdealloc : DeallocOkExt b A ext)
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (outA selfA msgA : BitVec 64) (R : SepProp) (s0 : State)
    (hinv0 : M.Inv s0) (hb : b &&& 0xfff#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = outA) (hx1 : s0.readReg64 .x1 = selfA) (hx2 : s0.readReg64 .x2 = msgA)
    (hinv : statesRecvPreInv (.ekReceivedCt1Sampled st)) (hsp0_align : s0.spAligned = true)
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
    (hrun0 : s0.status = .Running) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 Reg.lr) s0
      (stackAt s0.sp statesRecvStackX ∗ (M.P_stk s0.sp ∗ memRegion outA v1RecvSize ∗
        chunkedStatesAt A selfA (.ekReceivedCt1Sampled st) ∗
        messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (M.specOut st msg).post (outA, selfA, msgA) s0 sf ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) → sf.mem ⊨ (M.specOut st msg).onPanic (outA, selfA, msgA) s0 sf ∗ R) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue (b := b) (ext := ext) s0
    (M.P_stk s0.sp ∗ memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ekReceivedCt1Sampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine M.seq_p hinv0 hpro ?_
  intro s1 hpc1 hrun1 hinv1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  dsimp only [chunkedStatesAt]
  have hdisp := states_recv_dispatch_ekReceivedCt1Sampled hb s1 (s0.sp - 4240#64) selfA
    (M.P_stk s0.sp ∗ chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗
     statesRecvSavedCells s0) hpc1 hrun1 hsp1 hx1_1
  refine M.seq_p hinv1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hinv2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  set fsp := s0.sp - 4240#64
  have hpre_split :
      (selfA ↦₆₄ 10#64) ∗ statesRecvRoAt b ∗
      (M.P_stk s0.sp ∗ chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ w : Words66, ∃∗ sp : SendEkSpills, ∃∗ qac0 : BitVec 128, ∃∗ qf10 : BitVec 128,
        ⌜w.w65 = st.uc.epoch⌝ ∗
        (words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
         sendEkSpillsAt fsp sp ∗ ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
         (M.P_stk s0.sp ∗ (selfA ↦₆₄ 10#64) ∗
          relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
          memRegion (selfA + 536#64) 392 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
          statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗ A.pool ∗
          stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          ekUnusedRestAt fsp ∗ statesRecvSavedCells s0))) := by
    unfold messageAt
    have hex66 := chunkedEkReceivedCt1SampledAt_extract66 A (selfA + 8#64) st
    have hstk : memRegion fsp 4144 ⊢
        ∃∗ sp : SendEkSpills, ∃∗ qac0 : BitVec 128, ∃∗ qf10 : BitVec 128,
          sendEkSpillsAt fsp sp ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
          ((fsp + 2752#64) ↦₁₂₈ qac0) ∗ ((fsp + 3856#64) ↦₁₂₈ qf10) ∗ ekUnusedRestAt fsp := by
      refine Entails.trans (memRegion_4144_entails_sendEkFrame fsp) ?_
      apply Entails.sepExists_elim; intro sp
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sendEkUnusedAt_split_ek fsp))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply Entails.sepExists_elim; intro qac0; apply Entails.sepExists_elim; intro qf10
      exact Entails.sepExists_right sp (Entails.sepExists_right qac0
        (Entails.sepExists_right qf10 (Entails.of_eq (by sep_ac_rfl))))
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedEkReceivedCt1SampledAt A (selfA + 8#64) st ∗ memRegion fsp 4144 ∗
      (M.P_stk s0.sp ∗ (selfA ↦₆₄ 10#64) ∗ statesRecvRoAt b ∗ memRegion (selfA + 536#64) 392 ∗
       memRegion outA v1RecvSize ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
       A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hex66 (sepConj_mono_left hstk)) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro sp; apply Entails.sepExists_elim; intro qac0
    apply Entails.sepExists_elim; intro qf10; apply Entails.sepExists_elim; intro w
    exact Entails.sepExists_right w (Entails.sepExists_right sp
      (Entails.sepExists_right qac0 (Entails.sepExists_right qf10 (Entails.of_eq (by sep_ac_rfl)))))
  refine SepWPp.weaken_pre hpre_split ?_
  apply sepWPp_intro_ex hrun2; intro w; apply sepWPp_intro_ex hrun2; intro sp
  apply sepWPp_intro_ex hrun2; intro qac0; apply sepWPp_intro_ex hrun2; intro qf10
  apply SepWPp.pure_left; intro hw65
  refine M.seq_p hinv2 (ek_step_3392_3732 s2 fsp outA selfA msgA msg.epoch w sp qac0 qf10
    (M.P_stk s0.sp ∗ (selfA ↦₆₄ 10#64) ∗
     relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
     memRegion (selfA + 536#64) 392 ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗
     statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗ A.pool ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
     memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
     ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx24_2) ?_
  intro s3 hpc3 hrun3 hinv3 ⟨hsp3, h3_0, h3_1, h3_3, h3_4, h3_5, h3_6, h3_7, h3_10, h3_11,
    h3_12, h3_13, h3_14, h3_15, h3_17, h3_18, h3_19, h3_20, h3_21, h3_22, h3_23,
    h3_24, h3_25, h3_26, h3_27, h3_28, h3_30, h3_8, h3_z, htr3⟩
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans htr20
  rw [hw65] at h3_8 h3_z
  by_cases hgt : msg.epoch > st.uc.epoch
  · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 1#32 := ekCmpW8_of_gt hgt
    rw [hcmp] at h3_8 h3_z
    have hz_f : s3.pstate.z = false := h3_z
    have hrecv := states_recv_ekReceivedCt1Sampled_gt K st msg hgt
    have hexit := ek_gt_3732_ret hdealloc s0 s3 outA selfA msg.epoch st
      (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b)
      hsp0_align hpc3 hrun3 hsp3 hz_f h3_8 h3_0 h3_19 h3_25 htr30
    refine M.exit_p s0 s3 outA selfA msgA st msg _ R (SepWP.weaken_pre ?_ (SepWP.mono hexit ?_))
    · have hself := selfA_recompose_528 A selfA st w
      have hstk := ek_frame_entails_memRegion_4144 fsp (ekLoadSpills sp w) w.q60 w.q63
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        ((selfA ↦₆₄ 10#64) ∗
         (words66At (selfA + 8#64) w ∗
          relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w))) ∗
         memRegion (selfA + 536#64) 392) ∗
        (sendEkSpillsAt fsp (ekLoadSpills sp w) ∗ memRegion (fsp + 576#64) 376 ∗
         memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
         ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗ ekUnusedRestAt fsp) ∗
        (M.P_stk s0.sp ∗ ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
         statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗ A.pool ∗
         stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by sep_ac_rfl)) ?_
      exact Entails.trans (sepConj_mono hself (sepConj_mono_left hstk))
        (Entails.of_eq (by dsimp only [fsp]; sep_ac_rfl))
    · intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by sep_ac_rfl)
  · by_cases hlt : msg.epoch < st.uc.epoch
    · have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 255#32 := ekCmpW8_of_lt hlt
      rw [hcmp] at h3_8 h3_z
      have hz_f : s3.pstate.z = false := h3_z
      have hrecv := states_recv_ekReceivedCt1Sampled_lt K st msg hlt
      refine M.seq_p hinv3 (ek_step_3732_lt_10136 s3 fsp _ hpc3 hrun3 hsp3 hz_f h3_8) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, h4_1, h4_3, h4_4, h4_5, h4_6, h4_7, h4_10, h4_11,
        h4_12, h4_13, h4_14, h4_15, h4_17, h4_18, h4_19, h4_20, h4_21, h4_22, h4_23,
        h4_26, h4_27, _, h4_30, htr4⟩
      have hexit := ek_noop_10136_ret_gen M s0 s4 outA selfA st w sp
        (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
        hinv4 hsp0_align hpc4 hrun4 hsp4
        (h4_1.trans h3_1) (h4_3.trans h3_3) (h4_4.trans h3_4) (h4_5.trans h3_5)
        (h4_6.trans h3_6) (h4_7.trans h3_7) (h4_10.trans h3_10) (h4_11.trans h3_11)
        (h4_12.trans h3_12) (h4_13.trans h3_13) (h4_14.trans h3_14) (h4_15.trans h3_15)
        (h4_17.trans h3_17) (h4_18.trans h3_18) (h4_19.trans h3_19) (h4_20.trans h3_20)
        (h4_21.trans h3_21) (h4_22.trans h3_22) (h4_23.trans h3_23) (h4_26.trans h3_26)
        (h4_27.trans h3_27) (h4_30.trans h3_30) (htr4.trans htr30)
      refine M.exit_p s0 s4 outA selfA msgA st msg _ R
        (SepWP.weaken_pre (Entails.of_eq (by unfold messageAt; dsimp only [fsp]; sep_ac_rfl))
          (SepWP.mono hexit ?_))
      intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
      refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
      rw [hrecv]; exact Entails.of_eq (by sep_ac_rfl)
    · have heq : msg.epoch = st.uc.epoch :=
        BitVec.le_antisymm (BitVec.not_lt.mp hgt) (BitVec.not_lt.mp hlt)
      have hcmp : ekCmpW8 (subsPState64 msg.epoch st.uc.epoch) = 0#32 := ekCmpW8_of_eq heq
      rw [hcmp] at h3_z
      have hz_t : s3.pstate.z = true := h3_z
      refine M.seq_p hinv3 (ek_step_3732_eq_9064 s3 fsp _ hpc3 hrun3 hsp3 hz_t) ?_
      intro s4 hpc4 hrun4 hinv4 ⟨hsp4, h4_1, h4_3, h4_4, h4_5, h4_6, h4_7, h4_10, h4_11,
        h4_12, h4_13, h4_14, h4_15, h4_17, h4_18, h4_19, h4_20, h4_21, h4_22, h4_23,
        h4_24, h4_25, h4_26, h4_27, h4_28, _, h4_30, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans htr30
      by_cases hack : (match msg.payload with | .ct1Ack true => true | .ekCt1Ack _ => true | _ => false) = true
      · obtain ⟨outSt, hok⟩ := ekReceivedCt1Sampled_recv_ct1_ack_ok_of_preInv K st hinv
        have hstep_ack := ek_step_9064_ack_9344 hb s4 fsp msgA msg.payload
          (M.P_stk s0.sp ∗ words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
           sendEkSpillsAt fsp (ekLoadSpills sp w) ∗
           ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
           (selfA ↦₆₄ 10#64) ∗
           relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
           memRegion (selfA + 536#64) 392 ∗
           statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
           memRegion outA v1RecvSize ∗ A.pool ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hack hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine M.seq_p hinv4
          (SepWP.weaken_pre (Entails.of_eq (by dsimp only [statesRecvRoAt]; sep_ac_rfl)) hstep_ack) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, h5_1, h5_3, h5_4, h5_5, h5_6, h5_7, h5_10, h5_11,
          h5_12, h5_13, h5_14, h5_15, h5_17, h5_18, h5_19, h5_20, h5_21, h5_22, h5_23,
          h5_25, h5_26, h5_27, h5_28, _, h5_30, htr5⟩
        have h25_eq : s5.readReg64 .x25 = st.uc.epoch := by rw [h5_25, h4_25, h3_25, heq]
        refine SepWPp.weaken_pre (Entails.of_eq ?_)
          (ek_ack_9344_ok_ret_gen M hb s0 s5 outA selfA msgA st outSt msg w sp R
            hinv5 heq hack hok hsp0_align hpc5 hrun5 hsp5
            (h5_3.trans (h4_3.trans h3_3)) (h5_4.trans (h4_4.trans h3_4)) (h5_5.trans (h4_5.trans h3_5))
            (h5_6.trans (h4_6.trans h3_6)) (h5_7.trans (h4_7.trans h3_7)) (h5_10.trans (h4_10.trans h3_10))
            (h5_11.trans (h4_11.trans h3_11)) (h5_12.trans (h4_12.trans h3_12)) (h5_13.trans (h4_13.trans h3_13))
            (h5_14.trans (h4_14.trans h3_14)) (h5_15.trans (h4_15.trans h3_15)) (h5_17.trans (h4_17.trans h3_17))
            (h5_18.trans (h4_18.trans h3_18)) (h5_19.trans (h4_19.trans h3_19)) (h5_20.trans (h4_20.trans h3_20))
            (h5_21.trans (h4_21.trans h3_21)) (h5_22.trans (h4_22.trans h3_22)) (h5_23.trans (h4_23.trans h3_23))
            h25_eq (h5_26.trans (h4_26.trans h3_26)) (h5_27.trans (h4_27.trans h3_27))
            (h5_28.trans (h4_28.trans h3_28)) (h5_30.trans (h4_30.trans h3_30)) (htr5.trans htr40))
        unfold messageAt; dsimp only [statesRecvRoAt, fsp]; sep_ac_rfl
      · have hno : (match msg.payload with | .ct1Ack true => true | .ekCt1Ack _ => true | _ => false) = false :=
          Bool.eq_false_iff.mpr hack
        have hrecv := states_recv_ekReceivedCt1Sampled_eq_no_ack K st msg heq hno
        have hstep_no := ek_step_9064_no_ack_10136 s4 fsp msgA msg.payload
          (M.P_stk s0.sp ∗ words66At (selfA + 8#64) w ∗ (msgA ↦₆₄ msg.epoch) ∗
           sendEkSpillsAt fsp (ekLoadSpills sp w) ∗ ((fsp + 2752#64) ↦₁₂₈ w.q60) ∗ ((fsp + 3856#64) ↦₁₂₈ w.q63) ∗
           (selfA ↦₆₄ 10#64) ∗
           relocatedHeap (fun dst => chunkedEkReceivedCt1SampledAt A dst st) (wordsBytes (words66List w)) ∗
           memRegion (selfA + 536#64) 392 ∗ statesRecvRoAt b ∗ memRegion outA v1RecvSize ∗ A.pool ∗
           stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 576#64) 376 ∗
           memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 880 ∗
           ekUnusedRestAt fsp ∗ statesRecvSavedCells s0)
          hno hpc4 hrun4 hsp4 (h4_24.trans h3_24)
        refine M.seq_p hinv4 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hstep_no) ?_
        intro s5 hpc5 hrun5 hinv5 ⟨hsp5, h5_1, h5_3, h5_4, h5_5, h5_6, h5_7, h5_10, h5_11,
          h5_12, h5_13, h5_14, h5_15, h5_17, h5_18, h5_19, h5_20, h5_21, h5_22, h5_23,
          h5_26, h5_27, _, h5_30, htr5⟩
        have hexit := ek_noop_10136_ret_gen M s0 s5 outA selfA st w sp
          (M.P_stk s0.sp ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
          hinv5 hsp0_align hpc5 hrun5 hsp5
          (h5_1.trans (h4_1.trans h3_1)) (h5_3.trans (h4_3.trans h3_3)) (h5_4.trans (h4_4.trans h3_4))
          (h5_5.trans (h4_5.trans h3_5)) (h5_6.trans (h4_6.trans h3_6)) (h5_7.trans (h4_7.trans h3_7))
          (h5_10.trans (h4_10.trans h3_10)) (h5_11.trans (h4_11.trans h3_11)) (h5_12.trans (h4_12.trans h3_12))
          (h5_13.trans (h4_13.trans h3_13)) (h5_14.trans (h4_14.trans h3_14)) (h5_15.trans (h4_15.trans h3_15))
          (h5_17.trans (h4_17.trans h3_17)) (h5_18.trans (h4_18.trans h3_18)) (h5_19.trans (h4_19.trans h3_19))
          (h5_20.trans (h4_20.trans h3_20)) (h5_21.trans (h4_21.trans h3_21)) (h5_22.trans (h4_22.trans h3_22))
          (h5_23.trans (h4_23.trans h3_23)) (h5_26.trans (h4_26.trans h3_26)) (h5_27.trans (h4_27.trans h3_27))
          (h5_30.trans (h4_30.trans h3_30)) (htr5.trans htr40)
        refine M.exit_p s0 s5 outA selfA msgA st msg _ R
          (SepWP.weaken_pre (Entails.of_eq (by unfold messageAt; dsimp only [fsp]; sep_ac_rfl))
            (SepWP.mono hexit ?_))
        intro sf Pf _ _ ⟨hPf, hsp_sf, hcs_sf, htr_sf⟩
        refine ⟨Entails.trans hPf ?_, hsp_sf, hcs_sf, htr_sf⟩
        rw [hrecv]; exact Entails.of_eq (by sep_ac_rfl)

private def ekRecvMode_raw (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      (ekReceivedCt1SampledRecvCt1AckSpec A F K b)) : EkRecvMode A F K b ext where
  Inv := fun _ => True; P_stk := fun _ => emp
  specOut := fun st msg => statesRecvVariantSpec A F K b (.ekReceivedCt1Sampled st) msg
  seq := fun _ h1 h2 => seq_clean h1 fun sm hp hr hQ => h2 sm hp hr trivial hQ
  seq_p := fun _ h1 h2 => sepWPp_seq_clean h1 fun sm hp hr hQ => h2 sm hp hr trivial hQ
  writeback := fun hrel s0 s outA sp P_rest _ => states_recv_writeback_59e88 hmemcpy hrel s0 s outA sp P_rest
  exit_p := fun s0 s outA selfA msgA st msg P R h =>
    sepWPp_of_statesRecv_exit s0 s outA selfA msgA (.ekReceivedCt1Sampled st) msg P R
      (SepWP.mono h fun _ _ _ _ ⟨hPf, hsp, hcs, htr⟩ => ⟨Entails.trans hPf (by simp only [emp_sepConj]; exact Entails.refl _), hsp, hcs, htr⟩)
  call_ack := fun s0 s outA selfA msgA st outSt msg Frame R hb _ hok hfsp_align hpc hrun hsp hx0 hx1 hx2 hx19 hlr htr hnext => by
    refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      (memRegion ((s0.sp - 4240#64) + 976#64) chunkedCt2SampledSize ∗ chunkedEkReceivedCt1SampledAt A ((s0.sp - 4240#64) + 1856#64) st ∗
       unchunkedSendCt2RoAt b ∗ A.pool ∗ stackAt (s0.sp - 4240#64) ekReceivedCt1SampledRecvCt1AckStack) ∗
      (memRegion ((s0.sp - 4240#64) - 19552#64) 1920 ∗ Frame) by
        simp only [emp_sepConj, sepConj_emp, stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (s0.sp - 4240#64)]
        sep_ac_rfl)) ?_
    refine SepWPp.call hcall (x := ⟨(s0.sp - 4240#64) + 976#64, (s0.sp - 4240#64) + 1856#64, st, outSt⟩)
      (F := memRegion ((s0.sp - 4240#64) - 19552#64) 1920 ∗ Frame) hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr ?_
      (fun _ _ _ _ h => allowPanic_not_exited h) (fun sf _ hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    · intro R' hm; dsimp only [ekReceivedCt1SampledRecvCt1AckSpec]; rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨⟨hb, hx0, hx1, hx2, hok⟩, hm⟩
    · dsimp only [ekReceivedCt1SampledRecvCt1AckSpec, statesRecvVariantSpec, statesRecvOnPanic] at hmem ⊢
      refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
      unfold allocFailedIn at haf ⊢; rw [htr.1] at haf htr_sub; exact ⟨Or.inr haf, htr_sub⟩
    · dsimp only [ekReceivedCt1SampledRecvCt1AckSpec]; rw [hsp, sepConj_assoc]; refine SepWPp.pure_left fun htr_sf => ?_
      refine SepWPp.weaken_pre (Entails.of_eq ?_)
        (hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (hcs_sf.1.trans hx19) ⟨htr_sf.trans htr.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htr.2⟩ trivial)
      simp only [emp_sepConj, sepConj_emp, stackAt_statesRecvCallee_eq_ekReceivedCt1SampledRecvCt1Ack (s0.sp - 4240#64)]
      sep_ac_rfl

theorem states_recv_ekReceivedCt1Sampled_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) (ext : String → Option (State → State))
    (hdealloc : DeallocOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hcall : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr ekReceivedCt1SampledRecvCt1AckName)
      (ekReceivedCt1SampledRecvCt1AckSpec A F K b))
    (st : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.ekReceivedCt1Sampled st) msg) := by
  apply subroutine_ok_of_sepWPp; intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (emp ∗ memRegion outA v1RecvSize ∗
      chunkedStatesAt A selfA (.ekReceivedCt1Sampled st) ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool),
    R, Satisfies.mono (Entails.of_eq (by simp only [emp_sepConj, sepConj_emp]; sep_ac_rfl)) hmem,
    states_recv_ekReceivedCt1Sampled_sepWPp_gen (ekRecvMode_raw A F K b ext hmemcpy hcall)
      hdealloc st msg outA selfA msgA R s0 trivial hb hx0 hx1 hx2 hinv hsp0_align hpc0 hrun0⟩

end CryptoVerification.SpqrV1.States.Recv

