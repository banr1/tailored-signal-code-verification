/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 2: Arm 10 (`States.ct2Sampled`)

**Checked by Lean.**

Proves `states_into_pb_ct2Sampled` for Arm 10 (`States.ct2Sampled`, tag `12`, `+1432..+1540 -> +1544`)
of `<spqr::v1::chunked::states::States>::into_pb`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

@[local arm64_norm, local wp_norm]
theorem bv_sub_sub_lit (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local arm64_norm, local wp_norm]
theorem bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. Arm 10: `States.ct2Sampled` (`+0 -> +60 -> +1432 -> +1544 -> ret`) -/

theorem chunkedCt2Sampled_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.ct2Sampled s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        (stA ↦₆₄ 12#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        memRegion (stA + 464#64) 464 := by
  dsimp only [chunkedStatesAt, chunkedCt2SampledAt, unchunkedCt2SentAt]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left (authenticatorAt_expose A (stA + 8#64 + 400#64) s.uc.auth))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
  exact Entails.of_eq (by ac_rfl)

theorem stA_ct2Sampled_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 epoch : BitVec 64) :
    (stA ↦₆₄ 12#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
    ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
    ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
    ((stA + 456#64) ↦₆₄ epoch) ∗
    memRegion (stA + 464#64) 464 ⊢
    memRegion stA chunkedStatesSize := by
  have hc7 :
      ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
      ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
      ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ epoch) ⊢
      memRegion (stA + 408#64) 56 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 7 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right epoch (Entails.refl _)))))))
  have h1 : (stA ↦₆₄ 12#64) ⊢ memRegion stA 8 := Drop.pointsTo64_entails_memRegion stA 12#64
  have hsplit : memRegion stA chunkedStatesSize =
      memRegion stA 8 ∗
      memRegion (stA + 8#64) polyEncoderSize ∗
      memRegion (stA + 408#64) 56 ∗
      memRegion (stA + 464#64) 464 := by
    change memRegion stA 928 =
      memRegion stA 8 ∗ memRegion (stA + 8#64) 400 ∗
      memRegion (stA + 408#64) 56 ∗ memRegion (stA + 464#64) 464
    rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
          (b' := stA + 8#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
          (b' := stA + 408#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := stA + 408#64) (n := 56) (k := 464)
          (b' := stA + 464#64) rfl (by bv_omega) (by decide)]
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (show _ =
    (stA ↦₆₄ 12#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ epoch)) ∗
    memRegion (stA + 464#64) 464 by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono (Entails.refl _) (sepConj_mono hc7 (Entails.refl _)))

theorem outWords28_entails_ct2Sampled (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184
     w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x800000000000000a#64
      e0 e1 e2 e3 e4 e5 e6
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      w120 w128 w136 w144 w152 w160 w168 w176 w184
      w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ⊢
    optProtoInnerStateAt A out (States.ct2Sampled s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb,
    Unchunked.SendCt.Ct2Sent.into_pb, optProtoInnerStateAt, protoInnerStateAt,
    protoChunkedCt2SampledAt, optProtoPolynomialEncoderAt, Option.map,
    spqrPolyApi, pbToProtoPolyEncoder, protoPolyEncoderToPb,
    optProtoUnchunkedCt2SentAt, protoUnchunkedCt2SentAt,
    optProtoAuthenticatorAt_some_into_pb]
  have henc := protoPolynomialEncoder_of_words_heap A (out + 8#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb
  have hauth := authenticatorAt_of_words_heap A (out + 64#64)
    a0 a1 a2 a3 a4 a5 s.uc.auth
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at henc hauth ⊢
  have hc13 :
      ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗
      ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
      ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
      ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 120#64) 104 := by
    rw [ProofLib.memRegion_cells (out + 120#64) 13 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w120 (Entails.sepExists_right w128
      (Entails.sepExists_right w136 (Entails.sepExists_right w144
        (Entails.sepExists_right w152 (Entails.sepExists_right w160
          (Entails.sepExists_right w168 (Entails.sepExists_right w176
            (Entails.sepExists_right w184 (Entails.sepExists_right w192
              (Entails.sepExists_right w200 (Entails.sepExists_right w208
                (Entails.sepExists_right w216 (Entails.refl _)))))))))))))
  unfold outWords28
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 0x800000000000000a#64) ∗
    ((((out + 8#64) ↦₆₄ e0) ∗ ((out + 16#64) ↦₆₄ e1) ∗
      ((out + 24#64) ↦₆₄ e2) ∗ ((out + 32#64) ↦₆₄ e3) ∗
      ((out + 40#64) ↦₆₄ e4) ∗ ((out + 48#64) ↦₆₄ e5) ∗
      ((out + 56#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb) ∗
     ((((out + 64#64) ↦₆₄ a0) ∗ ((out + 72#64) ↦₆₄ a1) ∗
       ((out + 80#64) ↦₆₄ a2) ∗ ((out + 88#64) ↦₆₄ a3) ∗
       ((out + 96#64) ↦₆₄ a4) ∗ ((out + 104#64) ↦₆₄ a5) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
      ((out + 112#64) ↦₆₄ s.uc.epoch))) ∗
    (((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗
     ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
     ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
     ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
     ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
     ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
     ((out + 216#64) ↦₆₄ w216)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (sepConj_mono henc (sepConj_mono hauth (Entails.refl _))) hc13)

theorem states_into_pb_ct2Sampled_pre {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 60#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 1520#64)
    (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s1.readReg64 .x28 = s0.sp - 256#64)
    (hx27 : s1.readReg64 .x27 = s0.sp - 1360#64)
    (hx26 : s1.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : s1.readReg64 .x20 = stA)
    (hx19 : s1.readReg64 .x19 = out)
    (hx8 : s1.readReg64 .x8 = 12#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64) s1
      (memRegion (s0.sp - 480#64) 48 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbJumpTableAt b ∗
       Rest)
      (fun s2 P2 =>
        (P2 ⊢
          (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
           ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
           ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
           (stA ↦₆₄ 12#64) ∗
           ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
           statesIntoPbJumpTableAt b ∗
           Rest)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1480#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x27 = s0.sp - 1360#64 ∧
        s2.readReg64 .x21 = s.uc.epoch ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
  states_into_pb_fetches_range b (Rust.withPanics ext) 60 80
  states_into_pb_fetches_range b (Rust.withPanics ext) 1432 48
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hadrp hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  rw [ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
  cells_unfold
  wp_pull_exists
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

theorem states_into_pb_ct2Sampled_post (A : RustAlloc) (F : ShaCompress)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1480#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : sf.readReg64 .x27 = s0.sp - 1360#64)
    (hx21 : sf.readReg64 .x21 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
       ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
       ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 432#64) 128 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       cells (s0.sp - 1512#64) 19 ∗
       memRegion (s0.sp - 1304#64) 824 ∗
       cells (s0.sp - 304#64) 6 ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (StatesIntoPbPost A b s0 out stA (.ct2Sampled s)) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have h824 : memRegion (s0.sp - 1304#64) 824 =
      cells (s0.sp - 1304#64) 6 ∗ memRegion (s0.sp - 1256#64) 776 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 1304#64) (n := 48) (k := 776)
          (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1304#64) 6 (by decide)]
  rw [h824]
  cells_unfold
  wp_pull_exists
  rename_i u0 u1 u2 u3 u4 u5
    t0 t1 t2 t3 t4 t5
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) sf
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       ((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
       ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
       ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5) ∗
       memRegion (s0.sp - 432#64) 128 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       (((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
        ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
        ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
        ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
        ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
        ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
        ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
        ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
        ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
        ((s0.sp - 1368#64) ↦₆₄ w184)) ∗
       ((((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
         ((s0.sp - 1288#64) ↦₆₄ t2) ∗ ((s0.sp - 1280#64) ↦₆₄ t3) ∗
         ((s0.sp - 1272#64) ↦₆₄ t4) ∗ ((s0.sp - 1264#64) ↦₆₄ t5)) ∗
        memRegion (s0.sp - 1256#64) 776) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       memRegion (s0.sp - 256#64) 160 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 12#64) ∗
       ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       memRegion (stA + 464#64) 464 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            e0 e1 e2 e3 e4 e5
            a0 a1 a2 a3 a4 a5 s.uc.epoch w120
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTableAt b ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x800000000000000a#64 ∧
        s2.readReg64 .x21 = e6 ∧
        TraceCalleeSaved s2 s0) := by
    have hrejoin880 :
        (((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
         ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
         ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
         ((s0.sp - 1312#64) ↦₆₄ e6) ∗
         ((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
         ((s0.sp - 1288#64) ↦₆₄ a2) ∗ ((s0.sp - 1280#64) ↦₆₄ a3) ∗
         ((s0.sp - 1272#64) ↦₆₄ a4) ∗ ((s0.sp - 1264#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 1256#64) 776 ⊢
        memRegion (s0.sp - 1360#64) 880 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 104) (k := 776)
            (b' := s0.sp - 1256#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 1360#64) 13 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right e0 (Entails.sepExists_right e1
        (Entails.sepExists_right e2 (Entails.sepExists_right e3
          (Entails.sepExists_right e4 (Entails.sepExists_right e5
            (Entails.sepExists_right e6 (Entails.sepExists_right t0
              (Entails.sepExists_right t1 (Entails.sepExists_right a2
                (Entails.sepExists_right a3 (Entails.sepExists_right a4
                  (Entails.sepExists_right a5 (Entails.refl _)))))))))))))
    have hrejoin176 :
        (((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
         ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
         ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 432#64) 128 ⊢
        memRegion (s0.sp - 480#64) 176 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 48) (k := 128)
            (b' := s0.sp - 432#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 480#64) 6 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right a0 (Entails.sepExists_right a1
        (Entails.sepExists_right a2 (Entails.sepExists_right a3
          (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
    have hstA := stA_ct2Sampled_entails_928 stA a0 a1 a2 a3 a4 a5 s.uc.epoch
    refine SepWP.strengthen_entails_const (P₁ :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        e0 e1 e2 e3 e4 e5
        a0 a1 a2 a3 a4 a5 s.uc.epoch w120
        w128 w136 w144 w152 w160 w168 w176 w184
        0#64 w200 w208 w216 ∗
      ((((s0.sp - 1360#64) ↦₆₄ e0) ∗ ((s0.sp - 1352#64) ↦₆₄ e1) ∗
        ((s0.sp - 1344#64) ↦₆₄ e2) ∗ ((s0.sp - 1336#64) ↦₆₄ e3) ∗
        ((s0.sp - 1328#64) ↦₆₄ e4) ∗ ((s0.sp - 1320#64) ↦₆₄ e5) ∗
        ((s0.sp - 1312#64) ↦₆₄ e6) ∗
        ((s0.sp - 1304#64) ↦₆₄ t0) ∗ ((s0.sp - 1296#64) ↦₆₄ t1) ∗
        ((s0.sp - 1288#64) ↦₆₄ a2) ∗ ((s0.sp - 1280#64) ↦₆₄ a3) ∗
        ((s0.sp - 1272#64) ↦₆₄ a4) ∗ ((s0.sp - 1264#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 1256#64) 776) ∗
      ((((s0.sp - 480#64) ↦₆₄ a0) ∗ ((s0.sp - 472#64) ↦₆₄ a1) ∗
        ((s0.sp - 464#64) ↦₆₄ a2) ∗ ((s0.sp - 456#64) ↦₆₄ a3) ∗
        ((s0.sp - 448#64) ↦₆₄ a4) ∗ ((s0.sp - 440#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 432#64) 128) ∗
      memRegion (s0.sp - 256#64) 160 ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       ((stA ↦₆₄ 12#64) ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (stA + 464#64) 464) ∗
       statesIntoPbJumpTableAt b ∗ A.pool))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstA)))))))))) ?_
    states_into_pb_fetches_range b (Rust.withPanics ext) 1480 64
    dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
      epilogueStagingCells, BitVec.ofNat_eq_ofNat] at hpcf ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::into_pb" = entry
    examples_hide_fetches
    wp_steps
    refine Drop.align_pre (by ac_rfl) ?_
    wp_done
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (Drop.seq_clean hstep fun s2 hpc2 hrun2 ⟨hsp2, hx29_2, hx19_2, hx22_2, hx21_2, htr2⟩ => ?_)
  have hep := states_into_pb_epilogue s0 s2 out
    e0 e1 e2 e3 e4 e5
    a0 a1 a2 a3 a4 a5 s.uc.epoch w120
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_ct2Sampled A out
    e0 e1 e2 e3 e4 e5 e6
    a0 a1 a2 a3 a4 a5
    w120 w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x800000000000000a#64
      e0 e1 e2 e3 e4 e5 e6
      a0 a1 a2 a3 a4 a5 s.uc.epoch
      w120 w128 w136 w144 w152 w160 w168 w176 w184
      0#64 w200 w208 w216 ∗
     protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ct2.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

theorem states_into_pb_ct2Sampled {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b A ext)
    (s : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.ct2Sampled s)) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.ct2Sampled s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.ct2Sampled s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left (chunkedCt2Sampled_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
          (stA ↦₆₄ 12#64) ∗
          polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
          ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
          ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
          ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          memRegion (stA + 464#64) 464) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 12#64) ∗
        (polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
         ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         memRegion (stA + 464#64) 464 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTableAt b ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 ?_)))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 => ?_
  have hpro := states_into_pb_prologue_60 s0 out stA 12#64
    (polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
     ((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ s.uc.epoch) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  have h1416 : memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 1304#64) 824 ∗
      memRegion (s0.sp - 480#64) 48 ∗
      memRegion (s0.sp - 432#64) 128 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160 := by
    change memRegion (s0.sp - 1512#64) 1416 =
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 1360#64) 56 ∗
      memRegion (s0.sp - 1304#64) 824 ∗
      memRegion (s0.sp - 480#64) 48 ∗
      memRegion (s0.sp - 432#64) 128 ∗
      cells (s0.sp - 304#64) 6 ∗
      memRegion (s0.sp - 256#64) 160
    rw [ProofLib.memRegion_split' (b := s0.sp - 1512#64) (n := 152) (k := 1264)
          (b' := s0.sp - 1360#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 56) (k := 1208)
          (b' := s0.sp - 1304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 1304#64) (n := 824) (k := 384)
          (b' := s0.sp - 480#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 48) (k := 336)
          (b' := s0.sp - 432#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 432#64) (n := 128) (k := 208)
          (b' := s0.sp - 304#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 304#64) (n := 48) (k := 160)
          (b' := s0.sp - 256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_cells (s0.sp - 1512#64) 19 (by decide),
        ProofLib.memRegion_cells (s0.sp - 304#64) 6 (by decide)]
  rw [h1416]
  have hpre_step := states_into_pb_ct2Sampled_pre s0 s1 out stA s a0 a1 a2 a3 a4 a5
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 1304#64) 824 ∗
     memRegion (s0.sp - 432#64) 128 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 256#64) 160 ∗
     statesIntoPbSavedCells s0 ∗
     polyEncoderAt A (stA + 8#64) s.sending_ct2 ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     memRegion (stA + 464#64) 464 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre_step fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx29_2, hx27_2, hx21_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  refine call_encoderIntoPb_expose henc_raw (s0.sp - 1360#64) (stA + 8#64) s.sending_ct2
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 (by sep_focus)
    (fun sf e0 e1 e2 e3 e4 e5 e6 hpcf hrunf hspf hcsf htrf => ?_)
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_2
  have hx21_f : sf.readReg64 .x21 = s.uc.epoch := hcsf.2.2.1.trans hx21_2
  have hx27_f : sf.readReg64 .x27 = s0.sp - 1360#64 := hcsf.2.2.2.2.2.2.2.2.1.trans hx27_2
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_ct2Sampled_post A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 e0 e1 e2 e3 e4 e5 e6
    hsp0_align hpcf hrunf hspf hx29_f hx27_f hx21_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
