/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4b: Arm 6 (`States.headerReceived`)

**Checked by Lean.**

Verifies Arm 6 (`States.headerReceived`, tag `8`,
`+0 -> +60 -> +1240 -> +1344 -> +1428 -> +1544 -> ret`).
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
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## 1. Representation Exposure & Postcondition Entailments for Arm 6 (`HeaderReceived`) -/

/-- Expose `chunkedStatesAt A stA (.headerReceived s)` into tag `8#64`, 9 words (`a0..a5, h0..h2`)
    at `stA + 8..stA + 80`, `((stA + 80#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 88#64) s.receiving_ek`,
    `authenticatorHeap`, `vecU8Heap`, and trailing padding `memRegion (stA + 488#64) 440`. -/
theorem chunkedHeaderReceived_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.headerReceived s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ h0 : BitVec 64, ∃∗ h1 : BitVec 64, ∃∗ h2 : BitVec 64,
        (stA ↦₆₄ 8#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
         ((stA + 72#64) ↦₆₄ h2)) ∗
        (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A h0 h1 h2 s.uc.hdr ∗
        memRegion (stA + 488#64) 440 := by
  unfold chunkedStatesAt chunkedHeaderReceivedAt unchunkedHeaderReceivedAt
  have hauth := authenticatorAt_expose A (stA + 8#64) s.uc.auth
  have ha16 : (stA + 8#64) + 8#64 = stA + 16#64 := by bv_omega
  have ha24 : (stA + 8#64) + 16#64 = stA + 24#64 := by bv_omega
  have ha32 : (stA + 8#64) + 24#64 = stA + 32#64 := by bv_omega
  have ha40 : (stA + 8#64) + 32#64 = stA + 40#64 := by bv_omega
  have ha48 : (stA + 8#64) + 40#64 = stA + 48#64 := by bv_omega
  have ha56 : (stA + 8#64) + 48#64 = stA + 56#64 := by bv_omega
  have ha80 : (stA + 8#64) + 72#64 = stA + 80#64 := by bv_omega
  have ha88 : (stA + 8#64) + 80#64 = stA + 88#64 := by bv_omega
  rw [ha16, ha24, ha32, ha40, ha48] at hauth
  rw [ha56, ha80, ha88]
  have hhdr := vecU8_expose A (stA + 56#64) s.uc.hdr
  have hh64 : (stA + 56#64) + 8#64 = stA + 64#64 := by bv_omega
  have hh72 : (stA + 56#64) + 16#64 = stA + 72#64 := by bv_omega
  rw [hh64, hh72] at hhdr
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hhdr))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro h0
  apply Entails.sepExists_elim; intro h1
  apply Entails.sepExists_elim; intro h2
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right h0 (Entails.sepExists_right h1
          (Entails.sepExists_right h2 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` cells after Arm 6 (`headerReceived`) into `memRegion stA 928`. -/
theorem stA_headerReceived_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 h0 h1 h2 : BitVec 64) :
    (stA ↦₆₄ 8#64) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
     ((stA + 72#64) ↦₆₄ h2)) ∗
    memRegion (stA + 80#64) 408 ∗
    memRegion (stA + 488#64) 440 ⊢
    memRegion stA chunkedStatesSize := by
  have h80 :
      (stA ↦₆₄ 8#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) ⊢
      memRegion stA 80 := by
    rw [ProofLib.memRegion_cells stA 10 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right 8#64 (Entails.sepExists_right a0
      (Entails.sepExists_right a1 (Entails.sepExists_right a2
        (Entails.sepExists_right a3 (Entails.sepExists_right a4
          (Entails.sepExists_right a5 (Entails.sepExists_right h0
            (Entails.sepExists_right h1 (Entails.sepExists_right h2 ?_)))))))))
    exact Entails.of_eq (by ac_rfl)
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 80) (k := 848)
        (b' := stA + 80#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 80#64) (n := 408) (k := 440)
        (b' := stA + 488#64) rfl (by bv_omega) (by decide)]
  have hgroup :
      (stA ↦₆₄ 8#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) ∗
      memRegion (stA + 80#64) 408 ∗
      memRegion (stA + 488#64) 440 =
      ((stA ↦₆₄ 8#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
        ((stA + 72#64) ↦₆₄ h2))) ∗
      (memRegion (stA + 80#64) 408 ∗ memRegion (stA + 488#64) 440) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono h80 (Entails.refl _)

/-- Assemble `outWords28` for Arm 6 (`headerReceived`, tag `0x8000000000000006`) into
    `optProtoInnerStateAt A out (States.headerReceived s).into_pb.innerState`. -/
theorem outWords28_entails_headerReceived (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (h0 h1 h2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000006#64
      h0 h1 h2 a0 a1 a2
      a3 a4 a5 s.uc.epoch d0 d1 d2 d3
      d4 w128 w136 w144 w152 w160 w168 w176
      w184 w192 w200 w208 w216 ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A h0 h1 h2 s.uc.hdr ⊢
    optProtoInnerStateAt A out (States.headerReceived s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb,
    Unchunked.SendCt.HeaderReceived.into_pb, spqrPolyApi, spqrAuthApi,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderReceivedAt,
    optProtoUnchunkedHeaderReceivedAt, protoUnchunkedHeaderReceivedAt,
    optProtoPolynomialDecoderAt, Option.map,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hhdr := vecU8_of_words_heap A (out + 8#64) h0 h1 h2 s.uc.hdr
  have hh16 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have hh24 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  rw [hh16, hh24] at hhdr
  have hauth := authenticatorAt_of_words_heap A (out + 32#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have ha40 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have ha48 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  have ha56 : (out + 32#64) + 24#64 = out + 56#64 := by bv_omega
  have ha64 : (out + 32#64) + 32#64 = out + 64#64 := by bv_omega
  have ha72 : (out + 32#64) + 40#64 = out + 72#64 := by bv_omega
  rw [ha40, ha48, ha56, ha64, ha72] at hauth
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 88#64) d0 d1 d2 d3 d4 s.receiving_ek.intoPb
  have hd96 : (out + 88#64) + 8#64 = out + 96#64 := by bv_omega
  have hd104 : (out + 88#64) + 16#64 = out + 104#64 := by bv_omega
  have hd112 : (out + 88#64) + 24#64 = out + 112#64 := by bv_omega
  have hd120 : (out + 88#64) + 32#64 = out + 120#64 := by bv_omega
  rw [hd96, hd104, hd112, hd120] at hdec
  have ho32 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have ho80 : (out + 8#64) + 72#64 = out + 80#64 := by bv_omega
  have ho88 : (out + 8#64) + 80#64 = out + 88#64 := by bv_omega
  rw [ho32, ho80, ho88]
  have h96 :
      ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
      ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
      ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
      ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
      ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
      ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 128#64) 96 := by
    rw [ProofLib.memRegion_cells (out + 128#64) 12 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w128 (Entails.sepExists_right w136
      (Entails.sepExists_right w144 (Entails.sepExists_right w152
        (Entails.sepExists_right w160 (Entails.sepExists_right w168
          (Entails.sepExists_right w176 (Entails.sepExists_right w184
            (Entails.sepExists_right w192 (Entails.sepExists_right w200
              (Entails.sepExists_right w208 (Entails.sepExists_right w216
                (Entails.refl _))))))))))))
  unfold outWords28
  have hgroup :
      ((out ↦₆₄ 0x8000000000000006#64) ∗
       ((out + 8#64) ↦₆₄ h0) ∗ ((out + 16#64) ↦₆₄ h1) ∗
       ((out + 24#64) ↦₆₄ h2) ∗ ((out + 32#64) ↦₆₄ a0) ∗
       ((out + 40#64) ↦₆₄ a1) ∗ ((out + 48#64) ↦₆₄ a2) ∗
       ((out + 56#64) ↦₆₄ a3) ∗ ((out + 64#64) ↦₆₄ a4) ∗
       ((out + 72#64) ↦₆₄ a5) ∗ ((out + 80#64) ↦₆₄ s.uc.epoch) ∗
       ((out + 88#64) ↦₆₄ d0) ∗ ((out + 96#64) ↦₆₄ d1) ∗
       ((out + 104#64) ↦₆₄ d2) ∗ ((out + 112#64) ↦₆₄ d3) ∗
       ((out + 120#64) ↦₆₄ d4) ∗ ((out + 128#64) ↦₆₄ w128) ∗
       ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
       ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗
       ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
       ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) ∗
      protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A h0 h1 h2 s.uc.hdr =
      (out ↦₆₄ 0x8000000000000006#64) ∗
      (((((out + 8#64) ↦₆₄ h0) ∗ ((out + 16#64) ↦₆₄ h1) ∗
         ((out + 24#64) ↦₆₄ h2) ∗ vecU8Heap A h0 h1 h2 s.uc.hdr) ∗
        (((out + 32#64) ↦₆₄ a0) ∗ ((out + 40#64) ↦₆₄ a1) ∗
         ((out + 48#64) ↦₆₄ a2) ∗ ((out + 56#64) ↦₆₄ a3) ∗
         ((out + 64#64) ↦₆₄ a4) ∗ ((out + 72#64) ↦₆₄ a5) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
        ((out + 80#64) ↦₆₄ s.uc.epoch)) ∗
       (((out + 88#64) ↦₆₄ d0) ∗ ((out + 96#64) ↦₆₄ d1) ∗
        ((out + 104#64) ↦₆₄ d2) ∗ ((out + 112#64) ↦₆₄ d3) ∗
        ((out + 120#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb)) ∗
      (((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗
       ((out + 144#64) ↦₆₄ w144) ∗ ((out + 152#64) ↦₆₄ w152) ∗
       ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗
       ((out + 176#64) ↦₆₄ w176) ∗ ((out + 184#64) ↦₆₄ w184) ∗
       ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗
       ((out + 208#64) ↦₆₄ w208) ∗ ((out + 216#64) ↦₆₄ w216)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right
    (sepConj_mono
      (sepConj_mono (sepConj_mono hhdr (sepConj_mono_left hauth)) hdec)
      h96)

/-! ## 2. Proof of Arm 6: `States.headerReceived` (`+0 -> +60 -> +1240 -> +1344 -> +1428 -> +1544 -> ret`) -/

/-- Step 1 of Arm 6 (`+60 -> +96 -> +1240 -> +1256 -> memcpy`):
    dispatches on tag `8#64` (jump index `6` -> `+1240`) and sets up `memcpy(s0.sp - 1360#64, stA + 8#64, 480)`. -/
theorem states_into_pb_headerReceived_pre1
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (out stA : BitVec 64)
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
    (hx8 : s1.readReg64 .x8 = 8#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy")) s1
      (statesIntoPbJumpTableAt b ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTableAt b ∗ Rest) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1260#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        (s2.readReg64 .x2).toNat = 480 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧
        s2.readReg64 .x20 = stA ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
  states_into_pb_fetches_range b (Rust.withPanics ext) 60 80
  states_into_pb_fetches_range b (Rust.withPanics ext) 1240 20
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hadrp hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Step 2 of Arm 6 (`+1260 -> +1340 -> PolyDecoder::into_pb`):
    after `memcpy` returns to `+1260`, reads `a0..a5, h0..h2` from `stA + 8..stA + 80`, stages
    them at `s0.sp - 256..s0.sp - 184` (using `s0.sp - 160..s0.sp - 112` as scratch), loads
    `s.uc.epoch` from `s0.sp - 1288#64` into `x20`, and calls
    `<PolyDecoder>::into_pb(x0 = s0.sp - 400#64, x1 = s0.sp - 1280#64)`. -/
theorem states_into_pb_headerReceived_pre2
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 h0 h1 h2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1260#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr2 : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s2
      (cells (s0.sp - 256#64) 9 ∗
       cells (s0.sp - 160#64) 6 ∗
       ((s0.sp - 1288#64) ↦₆₄ epoch) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
        ((stA + 72#64) ↦₆₄ h2)) ∗
       Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
           ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
           ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
           ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
           ((s0.sp - 192#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗
          ((s0.sp - 1288#64) ↦₆₄ epoch) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
           ((stA + 72#64) ↦₆₄ h2)) ∗
          Rest) ∧
        s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1344#64 ∧
        s3.readReg64 .x0 = s0.sp - 400#64 ∧
        s3.readReg64 .x1 = s0.sp - 1280#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧
        s3.readReg64 .x20 = epoch ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0) := by
  rcases htr2 with ⟨htr2, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hrejoin48 :
      ((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
      ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
      ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5) ⊢
      memRegion (s0.sp - 160#64) 48 := by
    rw [ProofLib.memRegion_cells (s0.sp - 160#64) 6 (by decide)]
    cells_unfold
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5 (Entails.refl _))))))
  refine SepWP.strengthen_entails_const (P₁ :=
    (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
     ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
     ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
     ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
     ((s0.sp - 192#64) ↦₆₄ a5)) ∗
    (((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
     ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
     ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5)) ∗
    ((s0.sp - 1288#64) ↦₆₄ epoch) ∗
    (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
     ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
     ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
     ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
     ((stA + 72#64) ↦₆₄ h2)) ∗
    Rest)
    (sepConj_mono_right (sepConj_mono_left hrejoin48)) ?_
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  states_into_pb_fetches_range b (Rust.withPanics ext) 1260 84
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 of Arm 6 (`+1344 -> +1428 -> +1544 -> ret`):
    after `<PolyDecoder>::into_pb` returns to `+1344`, copies `h0..h2, a0..a5, s.uc.epoch, d0..d4`
    into the epilogue staging slots and runs `states_into_pb_epilogue`. -/
theorem states_into_pb_headerReceived_post (A : RustAlloc) (F : ShaCompress)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 h0 h1 h2 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1344#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx20 : sf.readReg64 .x20 = s.uc.epoch)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       cells (s0.sp - 480#64) 10 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 400#64) ↦₆₄ d0) ∗ ((s0.sp - 392#64) ↦₆₄ d1) ∗
        ((s0.sp - 384#64) ↦₆₄ d2) ∗ ((s0.sp - 376#64) ↦₆₄ d3) ∗
        ((s0.sp - 368#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
        memRegion (s0.sp - 1280#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
        ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 72 ∗
       ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 880#64) 400 ∗
       memRegion (s0.sp - 360#64) 56 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 8#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
        ((stA + 72#64) ↦₆₄ h2)) ∗
       memRegion (stA + 80#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A h0 h1 h2 s.uc.hdr ∗
       memRegion (stA + 488#64) 440 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (StatesIntoPbPost A b s0 out stA (.headerReceived s)) := by
  rcases htrf with ⟨htrf, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  rename_i u0 u1 u2 u3 u4 u5
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    w200 w208 w216 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 1544#64) sf
      ((((s0.sp - 1512#64) ↦₆₄ w200) ∗ ((s0.sp - 1504#64) ↦₆₄ w208) ∗
        ((s0.sp - 1496#64) ↦₆₄ w216) ∗ ((s0.sp - 1488#64) ↦₆₄ w64) ∗
        ((s0.sp - 1480#64) ↦₆₄ w72) ∗ ((s0.sp - 1472#64) ↦₆₄ w80) ∗
        ((s0.sp - 1464#64) ↦₆₄ w88) ∗ ((s0.sp - 1456#64) ↦₆₄ w96) ∗
        ((s0.sp - 1448#64) ↦₆₄ w104) ∗ ((s0.sp - 1440#64) ↦₆₄ w112) ∗
        ((s0.sp - 1432#64) ↦₆₄ w120) ∗ ((s0.sp - 1424#64) ↦₆₄ w128) ∗
        ((s0.sp - 1416#64) ↦₆₄ w136) ∗ ((s0.sp - 1408#64) ↦₆₄ w144) ∗
        ((s0.sp - 1400#64) ↦₆₄ w152) ∗ ((s0.sp - 1392#64) ↦₆₄ w160) ∗
        ((s0.sp - 1384#64) ↦₆₄ w168) ∗ ((s0.sp - 1376#64) ↦₆₄ w176) ∗
        ((s0.sp - 1368#64) ↦₆₄ w184)) ∗
       (((s0.sp - 480#64) ↦₆₄ c0) ∗ ((s0.sp - 472#64) ↦₆₄ c1) ∗
        ((s0.sp - 464#64) ↦₆₄ c2) ∗ ((s0.sp - 456#64) ↦₆₄ c3) ∗
        ((s0.sp - 448#64) ↦₆₄ c4) ∗ ((s0.sp - 440#64) ↦₆₄ c5) ∗
        ((s0.sp - 432#64) ↦₆₄ c6) ∗ ((s0.sp - 424#64) ↦₆₄ c7) ∗
        ((s0.sp - 416#64) ↦₆₄ c8) ∗ ((s0.sp - 408#64) ↦₆₄ c9)) ∗
       (((s0.sp - 304#64) ↦₆₄ u0) ∗ ((s0.sp - 296#64) ↦₆₄ u1) ∗
        ((s0.sp - 288#64) ↦₆₄ u2) ∗ ((s0.sp - 280#64) ↦₆₄ u3) ∗
        ((s0.sp - 272#64) ↦₆₄ u4) ∗ ((s0.sp - 264#64) ↦₆₄ u5)) ∗
       (((s0.sp - 400#64) ↦₆₄ d0) ∗ ((s0.sp - 392#64) ↦₆₄ d1) ∗
        ((s0.sp - 384#64) ↦₆₄ d2) ∗ ((s0.sp - 376#64) ↦₆₄ d3) ∗
        ((s0.sp - 368#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
        memRegion (s0.sp - 1280#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
        ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 72 ∗
       ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 880#64) 400 ∗
       memRegion (s0.sp - 360#64) 56 ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 8#64) ∗
       (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
        ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
        ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
        ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
        ((stA + 72#64) ↦₆₄ h2)) ∗
       memRegion (stA + 80#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A h0 h1 h2 s.uc.hdr ∗
       memRegion (stA + 488#64) 440 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            h0 h1 h2 a0 a1 a2
            a4 a5 s.uc.epoch d0 d1 d2 d3 d4
            w128 w136 w144 w152 w160 w168 w176 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A h0 h1 h2 s.uc.hdr ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTableAt b ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000006#64 ∧
        s2.readReg64 .x21 = a3 ∧
        TraceCalleeSaved s2 s0) := by
    have hrejoin880 :
        memRegion (s0.sp - 1360#64) 72 ∗
        ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (s0.sp - 1280#64) polyDecoderSize ∗
        memRegion (s0.sp - 880#64) 400 ⊢
        memRegion (s0.sp - 1360#64) 880 := by
      change memRegion (s0.sp - 1360#64) 72 ∗
        ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (s0.sp - 1280#64) 400 ∗
        memRegion (s0.sp - 880#64) 400 ⊢
        memRegion (s0.sp - 1360#64) 880
      rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 72) (k := 808)
            (b' := s0.sp - 1288#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 1288#64) (n := 8) (k := 800)
            (b' := s0.sp - 1280#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 1280#64) (n := 400) (k := 400)
            (b' := s0.sp - 880#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
    have hrejoin176 :
        (((s0.sp - 480#64) ↦₆₄ h0) ∗ ((s0.sp - 472#64) ↦₆₄ h1) ∗
         ((s0.sp - 464#64) ↦₆₄ h2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
         ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
         ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
         ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
         ((s0.sp - 400#64) ↦₆₄ d0) ∗ ((s0.sp - 392#64) ↦₆₄ d1) ∗
         ((s0.sp - 384#64) ↦₆₄ d2) ∗ ((s0.sp - 376#64) ↦₆₄ d3) ∗
         ((s0.sp - 368#64) ↦₆₄ d4)) ∗
        memRegion (s0.sp - 360#64) 56 ⊢
        memRegion (s0.sp - 480#64) 176 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 480#64) (n := 120) (k := 56)
            (b' := s0.sp - 360#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 480#64) 15 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right h0 (Entails.sepExists_right h1
        (Entails.sepExists_right h2 (Entails.sepExists_right a0
          (Entails.sepExists_right a1 (Entails.sepExists_right a2
            (Entails.sepExists_right a3 (Entails.sepExists_right a4
              (Entails.sepExists_right a5 (Entails.sepExists_right s.uc.epoch
                (Entails.sepExists_right d0 (Entails.sepExists_right d1
                  (Entails.sepExists_right d2 (Entails.sepExists_right d3
                    (Entails.sepExists_right d4 (Entails.refl _)))))))))))))))
    have hrejoin160 :
        (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
         ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
         ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
         ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
         ((s0.sp - 192#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 184#64) 24 ∗
        memRegion (s0.sp - 160#64) 48 ∗
        memRegion (s0.sp - 112#64) 16 ⊢
        memRegion (s0.sp - 256#64) 160 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 72) (k := 88)
            (b' := s0.sp - 184#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 184#64) (n := 24) (k := 64)
            (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 48) (k := 16)
            (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_cells (s0.sp - 256#64) 9 (by decide)]
      refine sepConj_mono_left ?_
      cells_unfold
      exact Entails.sepExists_right h0 (Entails.sepExists_right h1
        (Entails.sepExists_right h2 (Entails.sepExists_right a0
          (Entails.sepExists_right a1 (Entails.sepExists_right a2
            (Entails.sepExists_right a3 (Entails.sepExists_right a4
              (Entails.sepExists_right a5 (Entails.refl _)))))))))
    have hstA := stA_headerReceived_entails_928 stA a0 a1 a2 a3 a4 a5 h0 h1 h2
    refine SepWP.strengthen_entails_const (P₁ :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        h0 h1 h2 a0 a1 a2
        a4 a5 s.uc.epoch d0 d1 d2 d3 d4
        w128 w136 w144 w152 w160 w168 w176 w184
        0#64 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 72 ∗
       ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 1280#64) polyDecoderSize ∗
       memRegion (s0.sp - 880#64) 400) ∗
      ((((s0.sp - 480#64) ↦₆₄ h0) ∗ ((s0.sp - 472#64) ↦₆₄ h1) ∗
        ((s0.sp - 464#64) ↦₆₄ h2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
        ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
        ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
        ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
        ((s0.sp - 400#64) ↦₆₄ d0) ∗ ((s0.sp - 392#64) ↦₆₄ d1) ∗
        ((s0.sp - 384#64) ↦₆₄ d2) ∗ ((s0.sp - 376#64) ↦₆₄ d3) ∗
        ((s0.sp - 368#64) ↦₆₄ d4)) ∗
       memRegion (s0.sp - 360#64) 56) ∗
      ((((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
        ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A h0 h1 h2 s.uc.hdr ∗
       ((stA ↦₆₄ 8#64) ∗
        (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
         ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
         ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
         ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
         ((stA + 72#64) ↦₆₄ h2)) ∗
        memRegion (stA + 80#64) 408 ∗
        memRegion (stA + 488#64) 440) ∗
       statesIntoPbJumpTableAt b ∗ A.pool))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono hrejoin160
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstA))))))))))) ?_
    states_into_pb_fetches_range b (Rust.withPanics ext) 1344 88
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
    h0 h1 h2 a0 a1 a2
    a4 a5 s.uc.epoch d0 d1 d2 d3 d4
    w128 w136 w144 w152 w160 w168 w176 w184
    0#64 w200 w208 w216
    (protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A h0 h1 h2 s.uc.hdr ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_headerReceived A out
    h0 h1 h2 a0 a1 a2 a3 a4 a5 d0 d1 d2 d3 d4
    w128 w136 w144 w152 w160 w168 w176 w184 0#64 w200 w208 w216 s
  refine Entails.trans (Entails.of_eq (show _ =
    (outWords28 out
      0x8000000000000006#64
      h0 h1 h2 a0 a1 a2
      a3 a4 a5 s.uc.epoch d0 d1 d2 d3
      d4 w128 w136 w144 w152 w160 w168 w176
      w184 0#64 w200 w208 w216 ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ek.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A h0 h1 h2 s.uc.hdr) ∗
    (memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack) by ac_rfl)) ?_
  exact sepConj_mono_left hout

theorem stack_1416_split_headerReceived (sp0 : BitVec 64) :
    memRegion (sp0 - 1512#64) 1416 =
      cells (sp0 - 1512#64) 19 ∗
      memRegion (sp0 - 1360#64) 480 ∗
      memRegion (sp0 - 880#64) 400 ∗
      cells (sp0 - 480#64) 10 ∗
      memRegion (sp0 - 400#64) protoPolynomialDecoderSize ∗
      memRegion (sp0 - 360#64) 56 ∗
      cells (sp0 - 304#64) 6 ∗
      cells (sp0 - 256#64) 9 ∗
      memRegion (sp0 - 184#64) 24 ∗
      cells (sp0 - 160#64) 6 ∗
      memRegion (sp0 - 112#64) 16 := by
  change memRegion (sp0 - 1512#64) 1416 =
    cells (sp0 - 1512#64) 19 ∗
    memRegion (sp0 - 1360#64) 480 ∗
    memRegion (sp0 - 880#64) 400 ∗
    cells (sp0 - 480#64) 10 ∗
    memRegion (sp0 - 400#64) 40 ∗
    memRegion (sp0 - 360#64) 56 ∗
    cells (sp0 - 304#64) 6 ∗
    cells (sp0 - 256#64) 9 ∗
    memRegion (sp0 - 184#64) 24 ∗
    cells (sp0 - 160#64) 6 ∗
    memRegion (sp0 - 112#64) 16
  rw [ProofLib.memRegion_split' (b := sp0 - 1512#64) (n := 152) (k := 1264)
        (b' := sp0 - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1360#64) (n := 480) (k := 784)
        (b' := sp0 - 880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 880#64) (n := 400) (k := 384)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 80) (k := 304)
        (b' := sp0 - 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 400#64) (n := 40) (k := 264)
        (b' := sp0 - 360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 360#64) (n := 56) (k := 208)
        (b' := sp0 - 304#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 304#64) (n := 48) (k := 160)
        (b' := sp0 - 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 256#64) (n := 72) (k := 88)
        (b' := sp0 - 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 184#64) (n := 24) (k := 64)
        (b' := sp0 - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 160#64) (n := 48) (k := 16)
        (b' := sp0 - 112#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_cells (sp0 - 1512#64) 19 (by decide),
      ProofLib.memRegion_cells (sp0 - 480#64) 10 (by decide),
      ProofLib.memRegion_cells (sp0 - 304#64) 6 (by decide),
      ProofLib.memRegion_cells (sp0 - 256#64) 9 (by decide),
      ProofLib.memRegion_cells (sp0 - 160#64) 6 (by decide)]

set_option maxHeartbeats 800000 in
/-- Verifies `<States>::into_pb` on `.headerReceived s` (Arm 6, tag `8`). -/
theorem states_into_pb_headerReceived {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.headerReceived s)) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_raw hmemcpy
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.headerReceived s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.headerReceived s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedHeaderReceived_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
         ∃∗ h0 : BitVec 64, ∃∗ h1 : BitVec 64, ∃∗ h2 : BitVec 64,
          (stA ↦₆₄ 8#64) ∗
          (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
           ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
           ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
           ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
           ((stA + 72#64) ↦₆₄ h2)) ∗
          (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
           polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          vecU8Heap A h0 h1 h2 s.uc.hdr ∗
          memRegion (stA + 488#64) 440) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ h0 : BitVec 64, ∃∗ h1 : BitVec 64, ∃∗ h2 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗
        (stA ↦₆₄ 8#64) ∗
        ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
          ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
          ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
          ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
          ((stA + 72#64) ↦₆₄ h2)) ∗
         (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
          polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A h0 h1 h2 s.uc.hdr ∗
         memRegion (stA + 488#64) 440 ∗
         memRegion out optProtoInnerStateSize ∗
         statesIntoPbJumpTableAt b ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro a0
    apply Entails.sepExists_elim; intro a1
    apply Entails.sepExists_elim; intro a2
    apply Entails.sepExists_elim; intro a3
    apply Entails.sepExists_elim; intro a4
    apply Entails.sepExists_elim; intro a5
    apply Entails.sepExists_elim; intro h0
    apply Entails.sepExists_elim; intro h1
    apply Entails.sepExists_elim; intro h2
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right h0 (Entails.sepExists_right h1
            (Entails.sepExists_right h2 ?_))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 =>
    SepWPp.exists_elim fun h0 => SepWPp.exists_elim fun h1 =>
    SepWPp.exists_elim fun h2 => ?_
  have hpro := states_into_pb_prologue_60 s0 out stA 8#64
    ((((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
      ((stA + 72#64) ↦₆₄ h2)) ∗
     (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A h0 h1 h2 s.uc.hdr ∗
     memRegion (stA + 488#64) 440 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_headerReceived s0.sp]
  have hpre1 := states_into_pb_headerReceived_pre1 s0 s1 out stA
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 1360#64) 480 ∗
     memRegion (s0.sp - 880#64) 400 ∗
     cells (s0.sp - 480#64) 10 ∗
     memRegion (s0.sp - 400#64) protoPolynomialDecoderSize ∗
     memRegion (s0.sp - 360#64) 56 ∗
     cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 9 ∗
     memRegion (s0.sp - 184#64) 24 ∗
     cells (s0.sp - 160#64) 6 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 8#64) ∗
     (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
      ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
      ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
      ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
      ((stA + 72#64) ↦₆₄ h2)) ∗
     (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (stA + 88#64) s.receiving_ek) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A h0 h1 h2 s.uc.hdr ∗
     memRegion (stA + 488#64) 440 ∗
     memRegion out optProtoInnerStateSize ∗
     A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_words : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ a0) ∗ ((a + 8#64) ↦₆₄ a1) ∗ ((a + 16#64) ↦₆₄ a2) ∗
    ((a + 24#64) ↦₆₄ a3) ∗ ((a + 32#64) ↦₆₄ a4) ∗ ((a + 40#64) ↦₆₄ a5) ∗
    ((a + 48#64) ↦₆₄ h0) ∗ ((a + 56#64) ↦₆₄ h1) ∗ ((a + 64#64) ↦₆₄ h2)
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 8#64) s.receiving_ek
  have hF_src : F_words (stA + 8#64) =
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) := by
    dsimp only [F_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 72#64) =
      (((stA + 80#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (stA + 88#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 72#64) =
      (((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
       polyDecoderAt A (s0.sp - 1280#64) s.receiving_ek) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 72#64 = stA + 80#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate hmemcpy_raw
    (k := 72) (m := 408) (n := 480) (off := 72#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words9 a0 a1 a2 a3 a4 a5 h0 h1 h2)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_ek)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗
      memRegion (s0.sp - 880#64) 400 ∗
      cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 400#64) protoPolynomialDecoderSize ∗
      memRegion (s0.sp - 360#64) 56 ∗
      cells (s0.sp - 304#64) 6 ∗
      cells (s0.sp - 256#64) 9 ∗
      memRegion (s0.sp - 184#64) 24 ∗
      cells (s0.sp - 160#64) 6 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 8#64) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A h0 h1 h2 s.uc.hdr ∗
      memRegion (stA + 488#64) 440 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b ∗ A.pool)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_headerReceived_pre2 s0 s3 out stA
    a0 a1 a2 a3 a4 a5 h0 h1 h2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 72 ∗
     polyDecoderAt A (s0.sp - 1280#64) s.receiving_ek ∗
     memRegion (stA + 80#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
     ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗
     memRegion (s0.sp - 880#64) 400 ∗
     cells (s0.sp - 480#64) 10 ∗
     memRegion (s0.sp - 400#64) protoPolynomialDecoderSize ∗
     memRegion (s0.sp - 360#64) 56 ∗
     cells (s0.sp - 304#64) 6 ∗
     memRegion (s0.sp - 184#64) 24 ∗
     memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗
     (stA ↦₆₄ 8#64) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A h0 h1 h2 s.uc.hdr ∗
     memRegion (stA + 488#64) 440 ∗
     memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx20_4, hx19_4, htr4⟩ => ?_)
  refine call_decoderIntoPb_expose hdec_raw (s0.sp - 400#64) (s0.sp - 1280#64) s.receiving_ek
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗
      cells (s0.sp - 480#64) 10 ∗
      cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ h0) ∗ ((s0.sp - 248#64) ↦₆₄ h1) ∗
       ((s0.sp - 240#64) ↦₆₄ h2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
       ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
       ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗
      memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗
      ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 72 ∗
      ((s0.sp - 1288#64) ↦₆₄ s.uc.epoch) ∗
      memRegion (s0.sp - 880#64) 400 ∗
      memRegion (s0.sp - 360#64) 56 ∗
      statesIntoPbSavedCells s0 ∗
      (stA ↦₆₄ 8#64) ∗
      (((stA + 8#64) ↦₆₄ a0) ∗ ((stA + 16#64) ↦₆₄ a1) ∗
       ((stA + 24#64) ↦₆₄ a2) ∗ ((stA + 32#64) ↦₆₄ a3) ∗
       ((stA + 40#64) ↦₆₄ a4) ∗ ((stA + 48#64) ↦₆₄ a5) ∗
       ((stA + 56#64) ↦₆₄ h0) ∗ ((stA + 64#64) ↦₆₄ h1) ∗
       ((stA + 72#64) ↦₆₄ h2)) ∗
      memRegion (stA + 80#64) 408 ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A h0 h1 h2 s.uc.hdr ∗
      memRegion (stA + 488#64) 440 ∗
      memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun sf d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_4
  have hx20_f : sf.readReg64 .x20 = s.uc.epoch := hcsf.2.1.trans hx20_4
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_headerReceived_post A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 h0 h1 h2 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx20_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
