/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple3
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Relocatable `Ct2Sampled` Arm

Relocatable `[LibsignalPlacement]` proof of the `States.ct2Sampled` arm (`tag = 12#64`, `+2396`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `States.ct2Sampled` (`tag = 12#64`, `+2396` / `0x55db0`) -/

set_option maxHeartbeats 1600000 in
theorem ct2Sampled_step_le_2396_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp selfA msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 msg_epoch : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u224 u232 u240 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 : BitVec 64)
    (u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 : BitVec 64)
    (Frame : SepProp) (hle : ¬ (msg_epoch > w56)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
       (msgA ↦₆₄ msg_epoch) ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       epilogueRecvStackPartA488 fsp u224 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 ∗
       ((fsp + 232#64) ↦₆₄ u232) ∗ ((fsp + 240#64) ↦₆₄ u240) ∗
       epilogueRecvStackPartB fsp u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
            w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
            w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
          (msgA ↦₆₄ msg_epoch) ∗
          ct2SampledScratchLo fsp w52 w35 w32 w41 w40 w38 w34 w39 w36 w53 w37 w16 w47 w51 w49 w43 w45 w1 w48 ∗
          epilogueRecvStackPartA488 fsp 12#64 w7 w13 w12 w10 w5 w4 w11 w9 w8 w3 w2 w6 ∗
          ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w42) ∗
          epilogueRecvStackPartB fsp u248 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w39 ∧ sm.readReg64 .x1 = w0 ∧ sm.readReg64 .x3 = w29 ∧
        sm.readReg64 .x4 = w49 ∧ sm.readReg64 .x5 = w48 ∧ sm.readReg64 .x6 = w40 ∧ sm.readReg64 .x7 = w38 ∧
        sm.readReg64 .x8 = w1 ∧ sm.readReg64 .x9 = w43 ∧ sm.readReg64 .x10 = w35 ∧ sm.readReg64 .x11 = w34 ∧
        sm.readReg64 .x12 = w33 ∧ sm.readReg64 .x13 = w52 ∧ sm.readReg64 .x14 = w53 ∧ sm.readReg64 .x15 = w36 ∧
        sm.readReg64 .x16 = w55 ∧ sm.readReg64 .x17 = w45 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = w56 ∧ sm.readReg64 .x21 = w42 ∧ sm.readReg64 .x22 = w51 ∧ sm.readReg64 .x23 = w15 ∧
        sm.readReg64 .x24 = w31 ∧ sm.readReg64 .x25 = w32 ∧ sm.readReg64 .x26 = w47 ∧ sm.readReg64 .x27 = w16 ∧
        sm.readReg64 .x28 = w37 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w41 ∧
        TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch w56 = true := ule_true_of_not_gt hle
  dsimp only [lsProg_332, ct2SampledWords, words50List, ct2SampledScratchLo,
    wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, noneCap, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx1 hx24
  cases hule2 : BitVec.ule w56 msg_epoch <;> (wp_steps; wp_done)

set_option maxHeartbeats 1200000 in
theorem ct2Sampled_step_gt_ne_2396_10952_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp outA selfA msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 msg_epoch : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (v_out0 v_out16 : BitVec 64) (b_out8 : BitVec 8) (Frame : SepProp)
    (hgt : msg_epoch > w56) (hne : (msg_epoch == w56 + 1#64) = false) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 10952#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
       (msgA ↦₆₄ msg_epoch) ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
          ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
            w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
            w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
          (msgA ↦₆₄ msg_epoch) ∗
          ct2SampledScratchLo fsp w52 w35 w32 w41 w40 w38 w34 w39 w36 w53 w37 w16 w47 w51 w49 w43 w45 w1 w48 ∗
          ct2SampledScratchHi fsp w42 w7 w25 w12 w4 w11 w20 w23 w9 w44 w14 w8 w50 w3 w24 w54 w56 w2 w6 ∗
          Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = selfA + 8#64 ∧ TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch w56 = false := ule_false_of_gt hgt
  have hule2 : BitVec.ule w56 msg_epoch = true :=
    ule_true_of_not_gt (fun h => Nat.lt_asymm (BitVec.lt_def.mp hgt) (BitVec.lt_def.mp h))
  have hall : (w56 == 0xffffffffffffffff#64) = false := epoch_ne_allOnes_of_lt hgt
  have hz : (w56 + 1#64 == 0#64) = false :=
    ep_add_one_beq_zero_false (fun h => by rw [h] at hall; revert hall; decide)
  dsimp only [lsProg_332, ct2SampledWords, words50List, ct2SampledScratchLo, ct2SampledScratchHi,
    wordsAtOff, noneCap, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx19 hx1 hx24; wp_steps; wp_done

set_option maxHeartbeats 1600000 in
theorem ct2Sampled_step_gt_eq_2396_3328_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp selfA msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 msg_epoch : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : BitVec 64)
    (v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 : BitVec 64)
    (v40 v41 w_v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (Frame : SepProp) (hgt : msg_epoch > w56) (heq : (msg_epoch == w56 + 1#64) = true)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 3328#64) s
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
       ct2SampledWords fsp 1856 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
         v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39
         v40 v41 w_v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 ∗
       (msgA ↦₆₄ msg_epoch) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
            w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
            w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
          ct2SampledWords fsp 1856 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
            w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
            w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 ∗
          (msgA ↦₆₄ msg_epoch) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          ct2SampledScratchLo fsp w52 w35 w32 w41 w40 w38 w34 w39 w36 w53 w37 w16 w47 w51 w49 w43 w45 w1 w48 ∗
          ct2SampledScratchHi fsp w42 w7 w25 w12 w4 w11 w20 w23 w9 w44 w14 w8 w50 w3 w24 w54 w56 w2 w6 ∗
          Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = fsp + 976#64 ∧ sm.readReg64 .x1 = fsp + 1856#64 ∧
        sm.readReg64 .x2 = msg_epoch ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch w56 = false := ule_false_of_gt hgt
  have hule2 : BitVec.ule w56 msg_epoch = true :=
    ule_true_of_not_gt (fun h => Nat.lt_asymm (BitVec.lt_def.mp hgt) (BitVec.lt_def.mp h))
  have hall : (w56 == 0xffffffffffffffff#64) = false := epoch_ne_allOnes_of_lt hgt
  have hz : (w56 + 1#64 == 0#64) = false :=
    ep_add_one_beq_zero_false (fun h => by rw [h] at hall; revert hall; decide)
  have h_eq : msg_epoch = w56 + 1#64 := beq_iff_eq.mp heq
  dsimp only [lsProg_332, ct2SampledWords, words50List, ct2SampledScratchLo, ct2SampledScratchHi,
    wordsAtOff, lsLogFilterAddr, lsρ, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx1 hx24 h_eq; wp_steps 256; wp_done

theorem ct2Sampled_call_3328_3332_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F)))
    (s : State) (fsp msg_epoch : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (s' : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hnext : st.recv_next_epoch msg_epoch = .ok s') (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 3328#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = fsp + 976#64) (hx1 : s.readReg64 .x1 = fsp + 1856#64) (hx2 : s.readReg64 .x2 = msg_epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 3332#64) s
      (memRegion (fsp + 976#64) 56 ∗ chunkedCt2SampledAt A (fsp + 1856#64) st ∗
       A.pool ∗ stackAt fsp (dropGluePoly16Stack + 32) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ chunkedKeysUnsampledAt A (fsp + 976#64) s' ∗ memRegion (fsp + 1856#64) 456 ∗
          A.pool ∗ stackAt fsp (dropGluePoly16Stack + 32) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  dsimp only [lsProg_332] at hcall ⊢
  subst hsp hx2
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 355) ?_
  wp_steps
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hcall_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hcall hcl1
  dsimp only [withMemEq, ct2SampledRecvNextEpochSpec] at hcall_raw
  wp_call hcall_raw ⟨s.sp + 976#64, s.sp + 1856#64, st, s.readReg64 .x2, s'⟩
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem ct2Sampled_step_3332_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp msg_epoch : BitVec 64)
    (g' : AuthWords) (u224 u232 u368 u376 u456 u496 u504 : BitVec 64) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 3332#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s
      ((((fsp + 976#64) ↦₆₄ g'.v1.w0) ∗ ((fsp + 984#64) ↦₆₄ g'.v1.w1) ∗ ((fsp + 992#64) ↦₆₄ g'.v1.w2) ∗
        ((fsp + 1000#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 1008#64) ↦₆₄ g'.v2.w1) ∗ ((fsp + 1016#64) ↦₆₄ g'.v2.w2) ∗
        ((fsp + 1024#64) ↦₆₄ msg_epoch)) ∗
       (((fsp + 224#64) ↦₆₄ u224) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗ ((fsp + 376#64) ↦₆₄ u376) ∗
        ((fsp + 456#64) ↦₆₄ u456) ∗ ((fsp + 496#64) ↦₆₄ u496) ∗ ((fsp + 504#64) ↦₆₄ u504)) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (((fsp + 976#64) ↦₆₄ g'.v1.w0) ∗ ((fsp + 984#64) ↦₆₄ g'.v1.w1) ∗ ((fsp + 992#64) ↦₆₄ g'.v1.w2) ∗
           ((fsp + 1000#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 1008#64) ↦₆₄ g'.v2.w1) ∗ ((fsp + 1016#64) ↦₆₄ g'.v2.w2) ∗
           ((fsp + 1024#64) ↦₆₄ msg_epoch)) ∗
          (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 368#64) ↦₆₄ g'.v2.w2) ∗ ((fsp + 376#64) ↦₆₄ g'.v2.w1) ∗
           ((fsp + 456#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 496#64) ↦₆₄ g'.v1.w2) ∗ ((fsp + 504#64) ↦₆₄ msg_epoch)) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = g'.v1.w0 ∧ sm.readReg64 .x8 = g'.v1.w1 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  dsimp only [lsProg_332, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp; wp_steps; wp_done

theorem statesRecvRoPlacedAt_eq_log [LibsignalPlacement] :
    statesRecvRoPlacedAt =
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt) := by
  unfold statesRecvRoPlacedAt unchunkedSendCt2PlacedRoAt; ac_rfl

set_option maxHeartbeats 1600000 in
theorem states_recv_ct2Sampled_le_2396_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (g : AuthWords)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u0 u24 u32 u80 u88 u96 u136 u144 u152 : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 : BitVec 64)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.ct2Sampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  rw [ct2Sampled_recv_le st msg hle]; unfold messageAt
  have hstep1 := ct2Sampled_step_le_2396_18996_placed (ext := ext) s fsp selfA msgA
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
    w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch
    u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
    u224 u232 u240 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504
    u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488
    (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
     relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
     (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
     ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
     memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
     memRegion outA v1RecvSize ∗ messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗ A.pool)
    hle hfsp_align hpc hrun hsp hx1 hx24
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (SepWP.weaken_pre (Entails.of_eq ?_) hstep1) ?_
  · dsimp only [ct2SampledScratchHi, ct2SampledUntouchedHi, epilogueRecvStackPartA488, epilogueRecvStackPartB]; ac_rfl
  · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
      hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx21_1,
      hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, htr1⟩
    rw [hx19] at hx19_1
    have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
    have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
    refine SepWP.fold (ct2SampledLo_entails_memRegion_224 fsp g.v1.w2 w35 w32 w41 w40 w38 w34 w39 w36 g.v2.w0 w37 w16 w47 g.v1.w1 w49 w43 w45 w1 w48 u0 u24 u32 u80 u88 u96 u136 u144 u152) (by sep_focus) ?_
    refine SepWP.fold (selfA_ct2SampledWords_entails_memRegion_928 selfA w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch) (by sep_focus) ?_
    have hexit := epilogue_18996_exit_none_488_placed (A := A) hmemcpy s0 s1 outA
      12#64 w42 w7 w13 w12 w10 w5 w4 w11 w9 w8 w3 w2 w6
      u248 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 g.v1.w0 w24 w46 g.v2.w1 st.uc.epoch
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp10 hx19_1 htr10
    dsimp only at hexit; rw [← hfsp_eq] at hexit
    refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by unfold messageAt; ac_rfl)) hexit) ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    rw [hx0_1, hx1_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
        hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx20_1, hx21_1,
        hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx30_1] at hPf
    have hrec := ct2Sampled_out_recompose A outA st g w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 (s1.readReg64 .x2) u248 st.uc.epoch
    refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
      (epilogueRecvOutPartA outA 12#64 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
         w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 g.v1.w2 g.v2.w0 ∗
       epilogueRecvOutPartB488 outA w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
         w44 w45 w46 w47 g.v1.w0 g.v1.w1 g.v2.w1 g.v2.w2 st.uc.epoch (s1.readReg64 .x2) u248 st.uc.epoch ∗
       memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch))) ∗
      (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
      (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 1600000 in
theorem states_recv_ct2Sampled_gt_ne_2396_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec A F)))
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (g : AuthWords)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u0 u24 u32 u80 u88 u96 u136 u144 u152 : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hgt : msg.epoch > st.uc.epoch) (hne : (msg.epoch == st.uc.epoch + 1#64) = false)
    (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.ct2Sampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  rw [ct2Sampled_recv_gt_ne st msg hgt hne, memRegion_out_960_split_err outA]
  unfold messageAt; wp_pull_exists; rename_i v_out16 b_out8 v_out0
  have hstep1 := ct2Sampled_step_gt_ne_2396_10952_placed (ext := ext) s fsp outA selfA msgA
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
    w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch
    u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
    u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504
    v_out0 v_out16 b_out8
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
     relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
     relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
     (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
     ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
     ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
     memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt ∗ A.pool)
    hgt hne hfsp_align hpc hrun hsp hx19 hx1 hx24
  refine simple_seq_clean_lscl hcl (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, htr1⟩
  have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
  have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch) (by sep_focus) ?_
  refine SepWP.fold (ct2SampledWords_recompose A selfA 8 st g w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49) (by sep_focus) ?_
  refine SepWP.fold (ct2SampledLo_entails_memRegion_224 fsp g.v1.w2 w35 w32 w41 w40 w38 w34 w39 w36 g.v2.w0 w37 w16 w47 g.v1.w1 w49 w43 w45 w1 w48 u0 u24 u32 u80 u88 u96 u136 u144 u152) (by sep_focus) ?_
  refine SepWP.fold (ct2SampledHi_entails_memRegion_288 fsp w42 w7 w25 w12 w4 w11 w20 w23 w9 w44 w14 w8 g.v1.w0 w3 w24 g.v2.w1 st.uc.epoch w2 w6 u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stack_recombine_4144 fsp)) (by sep_focus) ?_
  have htail := states_recv_tail_drop_ct2Sampled_10952_placed hdrop s0 s1 (selfA + 8#64) st
    (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
    hsp0_align (by rwa [lsmpl_base_332_eq]) hrun1 hsp10 hx0_1 htr10 hcl1
  rw [← hfsp_eq] at htail
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by unfold messageAt; ac_rfl)) htail) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
    ((selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 8#64) chunkedCt2SampledSize ∗ memRegion (selfA + 464#64) 464) ∗
    (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
    (Entails.trans (sepConj_mono_left (selfA_ct2Sampled_entails_memRegion_928 selfA)) (Entails.of_eq (by unfold messageAt; ac_rfl)))),
    hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 1600000 in
theorem states_recv_ct2Sampled_gt_eq_2396_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 355)
      (withLsCodeLoaded lsmpl (ct2SampledRecvNextEpochSpec A F)))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (g : AuthWords)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u0 u24 u32 u80 u88 u96 u136 u144 u152 : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hgt : msg.epoch > st.uc.epoch) (heq : (msg.epoch == st.uc.epoch + 1#64) = true)
    (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2396#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.ct2Sampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  obtain ⟨hnext, hrecv⟩ := ct2Sampled_recv_gt_eq (K := K) st msg hgt heq
  rw [hrecv, memRegion_3632_split_976_1856 fsp, statesRecvRoPlacedAt_eq_log]
  have hpre :
      ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       (existsWordsAtOff fsp 57 1856 ∗ memRegion (fsp + 976#64) 56 ∗
        memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832) ∗
       stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       messageAt spqrPolyApi msgA msg ∗
       ((lsLogFilterAddr ↦₆₄ 0#64) ∗ (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt)) ∗ A.pool ⊢
      existsWordsAtOff fsp 57 1856 ∗
      (ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
         w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
         w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
       relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
       relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
       (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
       ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
       ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       memRegion (fsp + 976#64) 56 ∗ memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 ∗
       stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       messageAt spqrPolyApi msgA msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗ A.pool) :=
    Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex; intro v0; apply sepWP_intro_ex; intro v1; apply sepWP_intro_ex; intro v2; apply sepWP_intro_ex; intro v3; apply sepWP_intro_ex; intro v4; apply sepWP_intro_ex; intro v5
  apply sepWP_intro_ex; intro v6; apply sepWP_intro_ex; intro v7; apply sepWP_intro_ex; intro v8; apply sepWP_intro_ex; intro v9; apply sepWP_intro_ex; intro v10; apply sepWP_intro_ex; intro v11
  apply sepWP_intro_ex; intro v12; apply sepWP_intro_ex; intro v13; apply sepWP_intro_ex; intro v14; apply sepWP_intro_ex; intro v15; apply sepWP_intro_ex; intro v16; apply sepWP_intro_ex; intro v17
  apply sepWP_intro_ex; intro v18; apply sepWP_intro_ex; intro v19; apply sepWP_intro_ex; intro v20; apply sepWP_intro_ex; intro v21; apply sepWP_intro_ex; intro v22; apply sepWP_intro_ex; intro v23
  apply sepWP_intro_ex; intro v24; apply sepWP_intro_ex; intro v25; apply sepWP_intro_ex; intro v26; apply sepWP_intro_ex; intro v27; apply sepWP_intro_ex; intro v28; apply sepWP_intro_ex; intro v29
  apply sepWP_intro_ex; intro v30; apply sepWP_intro_ex; intro v31; apply sepWP_intro_ex; intro v32; apply sepWP_intro_ex; intro v33; apply sepWP_intro_ex; intro v34; apply sepWP_intro_ex; intro v35
  apply sepWP_intro_ex; intro v36; apply sepWP_intro_ex; intro v37; apply sepWP_intro_ex; intro v38; apply sepWP_intro_ex; intro v39; apply sepWP_intro_ex; intro v40; apply sepWP_intro_ex; intro v41
  apply sepWP_intro_ex; intro v42; apply sepWP_intro_ex; intro v43; apply sepWP_intro_ex; intro v44; apply sepWP_intro_ex; intro v45; apply sepWP_intro_ex; intro v46; apply sepWP_intro_ex; intro v47
  apply sepWP_intro_ex; intro v48; apply sepWP_intro_ex; intro v49
  apply sepWP_intro_ex; intro v50; apply sepWP_intro_ex; intro v51; apply sepWP_intro_ex; intro v52; apply sepWP_intro_ex; intro v53; apply sepWP_intro_ex; intro v54; apply sepWP_intro_ex; intro v55
  apply sepWP_intro_ex; intro v56; rw [emp_sepConj]; unfold messageAt
  have hstep1 := ct2Sampled_step_gt_eq_2396_3328_placed (ext := ext) s fsp selfA msgA
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
    w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch
    v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
    v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39
    v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56
    u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
    u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504
    (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
     relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ∗
     (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
     ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ∗
     ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
     memRegion (fsp + 976#64) 56 ∗ memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 ∗
     stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     (statesRecvJumpTablePlacedAt ∗ ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel) ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt) ∗ A.pool)
    hgt heq hfsp_align hpc hrun hsp hx1 hx24
  refine simple_seq_clean_lscl hcl (SepWP.weaken_pre (Entails.of_eq ?_) hstep1) ?_
  · dsimp only [ct2SampledWords, words50List, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx19_1, _, htr1⟩
    rw [hx19] at hx19_1
    refine SepWP.fold (ct2SampledWords_recompose A fsp 1856 st g w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49) (by sep_focus) ?_
    refine SepWP.fold (selfA_ct2SampledWords_entails_memRegion_928 selfA w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch) (by sep_focus) ?_
    refine SepWP.fold (ct2SampledLo_entails_memRegion_224 fsp g.v1.w2 w35 w32 w41 w40 w38 w34 w39 w36 g.v2.w0 w37 w16 w47 g.v1.w1 w49 w43 w45 w1 w48 u0 u24 u32 u80 u88 u96 u136 u144 u152) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq statesRecvRoPlacedAt_eq_log.symm) (by sep_focus) ?_
    refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_ct2SampledRecvNextEpoch fsp)) (by sep_focus) ?_
    have hstep2 := ct2Sampled_call_3328_3332_placed hcall s1 fsp msg.epoch st { uc := { epoch := msg.epoch, auth := st.uc.auth } }
      (memRegion (fsp - 19552#64) 15392 ∗ statesRecvRoPlacedAt ∗ memRegion fsp 224 ∗ memRegion selfA chunkedStatesSize ∗
       (msgA ↦₆₄ msg.epoch) ∗ ct2SampledScratchHi fsp w42 w7 w25 w12 w4 w11 w20 w23 w9 w44 w14 w8 g.v1.w0 w3 w24 g.v2.w1 st.uc.epoch w2 w6 ∗
       ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ∗
       memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ messagePayloadAt spqrPolyApi msgA msg.payload)
      hcl1 hnext hfsp_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx2_1
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep2) ?_
    intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, _, htr2⟩
    rw [hx19_1] at hx19_2
    refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_ct2SampledRecvNextEpoch fsp).symm) (by sep_focus) ?_
    refine SepWP.fold (chunkedKeysUnsampledAt_976_extract A fsp { uc := { epoch := msg.epoch, auth := st.uc.auth } }) (by sep_focus) ?_
    wp_pull_exists; rename_i g'
    have hstep3 := ct2Sampled_step_3332_18996_placed (ext := ext) s2 fsp msg.epoch g'
      u224 u232 u368 w4 w3 w2 w6
      (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g')) ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion (fsp + 1856#64) 456 ∗ A.pool ∗
       statesRecvRoPlacedAt ∗ memRegion fsp 224 ∗ memRegion selfA chunkedStatesSize ∗ (msgA ↦₆₄ msg.epoch) ∗
       (((fsp + 240#64) ↦₆₄ w42) ∗ ((fsp + 288#64) ↦₆₄ w7) ∗ ((fsp + 304#64) ↦₆₄ w25) ∗ ((fsp + 336#64) ↦₆₄ w12) ∗
        ((fsp + 384#64) ↦₆₄ w11) ∗ ((fsp + 392#64) ↦₆₄ w20) ∗ ((fsp + 400#64) ↦₆₄ w23) ∗ ((fsp + 408#64) ↦₆₄ w9) ∗
        ((fsp + 416#64) ↦₆₄ w44) ∗ ((fsp + 424#64) ↦₆₄ w14) ∗ ((fsp + 432#64) ↦₆₄ w8) ∗ ((fsp + 448#64) ↦₆₄ g.v1.w0) ∗
        ((fsp + 464#64) ↦₆₄ w24) ∗ ((fsp + 480#64) ↦₆₄ g.v2.w1) ∗ ((fsp + 488#64) ↦₆₄ st.uc.epoch)) ∗
       (((fsp + 248#64) ↦₆₄ u248) ∗ ((fsp + 256#64) ↦₆₄ u256) ∗ ((fsp + 264#64) ↦₆₄ u264) ∗ ((fsp + 272#64) ↦₆₄ u272) ∗
        ((fsp + 280#64) ↦₆₄ u280) ∗ ((fsp + 296#64) ↦₆₄ u296) ∗ ((fsp + 312#64) ↦₆₄ u312) ∗ ((fsp + 320#64) ↦₆₄ u320) ∗
        ((fsp + 328#64) ↦₆₄ u328) ∗ ((fsp + 344#64) ↦₆₄ u344) ∗ ((fsp + 352#64) ↦₆₄ u352) ∗ ((fsp + 360#64) ↦₆₄ u360) ∗
        ((fsp + 440#64) ↦₆₄ u440) ∗ ((fsp + 472#64) ↦₆₄ u472)) ∗
       memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ messagePayloadAt spqrPolyApi msgA msg.payload)
      hfsp_align hpc2 hrun2 hsp2
    refine CryptoVerification.SpqrV1.States.Recv.seq_clean (SepWP.weaken_pre (Entails.of_eq ?_) hstep3) ?_
    · dsimp only [ct2SampledScratchHi, ct2SampledUntouchedHi]; ac_rfl
    · intro s3 hpc3 hrun3 ⟨hsp3, hx1_3, hx8_3, hx19_3, _, htr3⟩
      rw [hx19_2] at hx19_3
      have htr30 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans (htr1.trans htr))
      have hsp30 : s3.sp = s0.sp - 4240#64 := by rw [hsp3, hfsp_eq]
      refine SepWP.fold (ct2Sampled_recombine_3632 fsp g' msg.epoch) (by sep_focus) ?_
      have hexit := epilogue_18996_exit_none_488_placed (A := A) hmemcpy s0 s3 outA
        2#64 w42 w7 u296 w12 u352 g'.v2.w2 g'.v2.w1 w11 w9 w8 g'.v2.w0 g'.v1.w2 msg.epoch
        u248 u256 u264 u272 u280 w25 u312 u320 u328 u344 u360 w20 w23 w44 w14 u440 g.v1.w0 w24 u472 g.v2.w1 st.uc.epoch
        (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g')) ∗
         memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
        hsp0_align hpc3 hrun3 hsp30 hx19_3 htr30
      dsimp only at hexit; rw [← hfsp_eq] at hexit
      refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq ?_) hexit) ?_
      · unfold messageAt; dsimp only [epilogueRecvStackPartA488, epilogueRecvStackPartB]; ac_rfl
      · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        rw [hx1_3, hx8_3] at hPf
        have hrec := keysUnsampled_out_recompose A outA { uc := { epoch := msg.epoch, auth := st.uc.auth } } g'
          w7 w8 w9 u352 w11 w12 u296
          (s3.readReg64 .x25) (s3.readReg64 .x12) (s3.readReg64 .x11) (s3.readReg64 .x10)
          (s3.readReg64 .x15) (s3.readReg64 .x28) (s3.readReg64 .x7) (s3.readReg64 .x0)
          (s3.readReg64 .x6) (s3.readReg64 .x30) (s3.readReg64 .x21) (s3.readReg64 .x9)
          (s3.readReg64 .x5) (s3.readReg64 .x4) (s3.readReg64 .x13) (s3.readReg64 .x14)
          w14 (s3.readReg64 .x23) (s3.readReg64 .x27) u440 u264 u344 w20 u272 u360 w23 w24 w25
          u328 u280 u320 (s3.readReg64 .x3) u312 (s3.readReg64 .x24) w44 (s3.readReg64 .x17) u472 (s3.readReg64 .x26)
          g.v1.w0 (s3.readReg64 .x22) g.v2.w1 (s3.readReg64 .x16) st.uc.epoch (s3.readReg64 .x2) u248 (s3.readReg64 .x20)
        refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
          (epilogueRecvOutPartA outA 2#64 g'.v1.w0 g'.v1.w1 g'.v1.w2 g'.v2.w0 g'.v2.w1 g'.v2.w2 msg.epoch
             w7 w8 w9 u352 w11 w12 u296
             (s3.readReg64 .x25) (s3.readReg64 .x12) (s3.readReg64 .x11) (s3.readReg64 .x10)
             (s3.readReg64 .x15) (s3.readReg64 .x28) (s3.readReg64 .x7) (s3.readReg64 .x0)
             (s3.readReg64 .x6) (s3.readReg64 .x30) (s3.readReg64 .x21) (s3.readReg64 .x9)
             (s3.readReg64 .x5) (s3.readReg64 .x4) (s3.readReg64 .x13) (s3.readReg64 .x14) ∗
           epilogueRecvOutPartB488 outA
             w14 (s3.readReg64 .x23) (s3.readReg64 .x27) u440 u264 u344 w20 u272 u360 w23 w24 w25
             u328 u280 u320 (s3.readReg64 .x3) u312 (s3.readReg64 .x24) w44 (s3.readReg64 .x17) u472 (s3.readReg64 .x26)
             g.v1.w0 (s3.readReg64 .x22) g.v2.w1 (s3.readReg64 .x16) st.uc.epoch (s3.readReg64 .x2) u248 (s3.readReg64 .x20) ∗
           memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
           relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g'))) ∗
          (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
           statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
          (Entails.trans (sepConj_mono_left hrec) (Entails.of_eq (by unfold messageAt; rw [statesRecvRoPlacedAt_eq_log]; ac_rfl)))),
          hsp_f, hcs_f, htr_f⟩

set_option maxHeartbeats 1600000 in
theorem states_recv_ct2Sampled_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.ct2Sampled st) msg)) := by
  refine subroutine_ok_statesRecvVariantPlacedSpec_of_sepWP (.ct2Sampled st) msg ?_
  intro outA selfA msgA s0 hcl hpc0 hrun0 hsp0_align hx0 hx1 hx2 _
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.ct2Sampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine simple_seq_clean_lscl hcl hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; rw [chunkedStatesAt_ct2Sampled_unfold]
  have hdisp := states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 12#64
    (chunkedCt2SampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine simple_seq_clean_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [lsmpl_base_332_eq] at hpc2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  let fsp := s0.sp - 4240#64
  rw [memRegion_4144_split_512 fsp]
  have hpre :
      (selfA ↦₆₄ 12#64) ∗ statesRecvRoPlacedAt ∗
      (chunkedCt2SampledAt A (selfA + 8#64) st ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗
       (existsWordsAtOff fsp 64 0 ∗ memRegion (fsp + 512#64) 3632) ∗ statesRecvSavedCells s0) ⊢
      (existsWordsWithBytesAtOff selfA (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2)) 50 8 ∗
       ((∃∗ g : AuthWords, wordsAtOff selfA (ct2SentWordsList g st.uc.epoch) 408 ∗
           relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch))) ∗
        existsWordsAtOff fsp 64 0)) ∗
      ((selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 464#64) 464 ∗
       memRegion (fsp + 512#64) 3632 ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
       memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (chunkedCt2SampledAt_extract_self A selfA st)))) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsWithBytesAtOff, existsWordsAtOff, wordsBytes, HAppend.hAppend, Append.append, List.append,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]
  apply sepWP_intro_ex_nest; intro w0; apply sepWP_intro_ex_nest; intro w1; apply sepWP_intro_ex_nest; intro w2; apply sepWP_intro_ex_nest; intro w3; apply sepWP_intro_ex_nest; intro w4; apply sepWP_intro_ex_nest; intro w5
  apply sepWP_intro_ex_nest; intro w6; apply sepWP_intro_ex_nest; intro w7; apply sepWP_intro_ex_nest; intro w8; apply sepWP_intro_ex_nest; intro w9; apply sepWP_intro_ex_nest; intro w10; apply sepWP_intro_ex_nest; intro w11
  apply sepWP_intro_ex_nest; intro w12; apply sepWP_intro_ex_nest; intro w13; apply sepWP_intro_ex_nest; intro w14; apply sepWP_intro_ex_nest; intro w15; apply sepWP_intro_ex_nest; intro w16; apply sepWP_intro_ex_nest; intro w17
  apply sepWP_intro_ex_nest; intro w18; apply sepWP_intro_ex_nest; intro w19; apply sepWP_intro_ex_nest; intro w20; apply sepWP_intro_ex_nest; intro w21; apply sepWP_intro_ex_nest; intro w22; apply sepWP_intro_ex_nest; intro w23
  apply sepWP_intro_ex_nest; intro w24; apply sepWP_intro_ex_nest; intro w25; apply sepWP_intro_ex_nest; intro w26; apply sepWP_intro_ex_nest; intro w27; apply sepWP_intro_ex_nest; intro w28; apply sepWP_intro_ex_nest; intro w29
  apply sepWP_intro_ex_nest; intro w30; apply sepWP_intro_ex_nest; intro w31; apply sepWP_intro_ex_nest; intro w32; apply sepWP_intro_ex_nest; intro w33; apply sepWP_intro_ex_nest; intro w34; apply sepWP_intro_ex_nest; intro w35
  apply sepWP_intro_ex_nest; intro w36; apply sepWP_intro_ex_nest; intro w37; apply sepWP_intro_ex_nest; intro w38; apply sepWP_intro_ex_nest; intro w39; apply sepWP_intro_ex_nest; intro w40; apply sepWP_intro_ex_nest; intro w41
  apply sepWP_intro_ex_nest; intro w42; apply sepWP_intro_ex_nest; intro w43; apply sepWP_intro_ex_nest; intro w44; apply sepWP_intro_ex_nest; intro w45; apply sepWP_intro_ex_nest; intro w46; apply sepWP_intro_ex_nest; intro w47
  apply sepWP_intro_ex_nest; intro w48; apply sepWP_intro_ex_nest; intro w49
  rw [sepConj_assoc (relocatedHeap _ _), sepConj_left_comm (relocatedHeap _ _)]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro u0; apply sepWP_intro_ex; intro u8; apply sepWP_intro_ex; intro u16; apply sepWP_intro_ex; intro u24; apply sepWP_intro_ex; intro u32; apply sepWP_intro_ex; intro u40
  apply sepWP_intro_ex; intro u48; apply sepWP_intro_ex; intro u56; apply sepWP_intro_ex; intro u64; apply sepWP_intro_ex; intro u72; apply sepWP_intro_ex; intro u80; apply sepWP_intro_ex; intro u88
  apply sepWP_intro_ex; intro u96; apply sepWP_intro_ex; intro u104; apply sepWP_intro_ex; intro u112; apply sepWP_intro_ex; intro u120; apply sepWP_intro_ex; intro u128; apply sepWP_intro_ex; intro u136
  apply sepWP_intro_ex; intro u144; apply sepWP_intro_ex; intro u152; apply sepWP_intro_ex; intro u160; apply sepWP_intro_ex; intro u168; apply sepWP_intro_ex; intro u176; apply sepWP_intro_ex; intro u184
  apply sepWP_intro_ex; intro u192; apply sepWP_intro_ex; intro u200; apply sepWP_intro_ex; intro u208; apply sepWP_intro_ex; intro u216
  apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232; apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264
  apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280; apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312
  apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328; apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360
  apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376; apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408
  apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424; apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456
  apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472; apply sepWP_intro_ex; intro u480; apply sepWP_intro_ex; intro u488; apply sepWP_intro_ex; intro u496; apply sepWP_intro_ex; intro u504
  rw [emp_sepConj]
  refine SepWP.weaken_pre (Entails.of_eq ?_) (by
    by_cases hgt : msg.epoch > st.uc.epoch
    · cases heq : (msg.epoch == st.uc.epoch + 1#64)
      · exact states_recv_ct2Sampled_gt_ne_2396_placed hC.hdrop_ct2_sampled s0 s2 fsp outA selfA msgA st msg g
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
          u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
          u0 u24 u32 u80 u88 u96 u136 u144 u152
          u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504
          u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472
          hcl2 hgt heq rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx24_2 htr20
      · exact states_recv_ct2Sampled_gt_eq_2396_placed hC.ct2SampledRecvNextEpoch_ok hC.hmemcpy_sat s0 s2 fsp outA selfA msgA st msg g
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
          u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
          u0 u24 u32 u80 u88 u96 u136 u144 u152
          u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504
          u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472
          hcl2 hgt heq rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx24_2 htr20
    · exact states_recv_ct2Sampled_le_2396_placed hC.hmemcpy_sat s0 s2 fsp outA selfA msgA st msg g
        w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
        u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216
        u0 u24 u32 u80 u88 u96 u136 u144 u152
        u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504
        u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472
        hgt rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx24_2 htr20)
  dsimp only [ct2SampledWords, words50List, ct2SentWordsList, authWordsList, wordsBytes, HAppend.hAppend, Append.append, List.append,
    wordsAtOff, ct2SampledScratchLo, ct2SampledUntouchedLo, ct2SampledScratchHi, ct2SampledUntouchedHi, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  ac_rfl

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct2Sampled_step_le_2396_18996_placed
  ct2Sampled_step_gt_ne_2396_10952_placed
  ct2Sampled_step_gt_eq_2396_3328_placed
  ct2Sampled_call_3328_3332_placed
  ct2Sampled_step_3332_18996_placed
  statesRecvRoPlacedAt_eq_log
  states_recv_ct2Sampled_le_2396_placed
  states_recv_ct2Sampled_gt_ne_2396_placed
  states_recv_ct2Sampled_gt_eq_2396_placed
  states_recv_ct2Sampled_placed_ok_ext
)

end CryptoVerification.SpqrV1.States.Recv
