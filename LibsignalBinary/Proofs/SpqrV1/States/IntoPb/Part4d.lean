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
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4d: Arm 2 (`States.headerSent`)

**Checked by Lean.**

Verifies Arm 2 (`States.headerSent`, tag `4`,
`+0 -> +60 -> +472 -> +500 -> +592 -> +604 -> +704 -> +1544 -> ret`).
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

/-! ## 1. Representation Exposure & Postcondition Entailments for Arm 2 (`HeaderSent`) -/

/-- Expose `chunkedStatesAt A stA (.headerSent s)` into tag `4#64`, `polyEncoderAt A (stA + 8#64) s.sending_ek`,
    9 words (`a0..a5, k0..k2`) at `stA + 408..stA + 480`, `((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1`,
    `authenticatorHeap`, `vecU8Heap`, and trailing padding `memRegion (stA + 888#64) 40`. -/
theorem chunkedHeaderSent_expose (A : RustAlloc) {F : ShaCompress} (stA : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A stA (.headerSent s) ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
        (stA ↦₆₄ 4#64) ∗
        polyEncoderAt A (stA + 8#64) s.sending_ek ∗
        (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
         ((stA + 472#64) ↦₆₄ k2)) ∗
        (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗
         polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
        authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
        vecU8Heap A k0 k1 k2 s.uc.dk ∗
        memRegion (stA + 888#64) 40 := by
  unfold chunkedStatesAt chunkedHeaderSentAt unchunkedEkSentAt
  have ha408 : (stA + 8#64) + 400#64 = stA + 408#64 := by bv_omega
  have ha488 : (stA + 8#64) + 480#64 = stA + 488#64 := by bv_omega
  rw [ha408, ha488]
  have hauth := authenticatorAt_expose A (stA + 408#64) s.uc.auth
  have ha416 : (stA + 408#64) + 8#64 = stA + 416#64 := by bv_omega
  have ha424 : (stA + 408#64) + 16#64 = stA + 424#64 := by bv_omega
  have ha432 : (stA + 408#64) + 24#64 = stA + 432#64 := by bv_omega
  have ha440 : (stA + 408#64) + 32#64 = stA + 440#64 := by bv_omega
  have ha448 : (stA + 408#64) + 40#64 = stA + 448#64 := by bv_omega
  have ha456 : (stA + 408#64) + 48#64 = stA + 456#64 := by bv_omega
  have ha480 : (stA + 408#64) + 72#64 = stA + 480#64 := by bv_omega
  rw [ha416, ha424, ha432, ha440, ha448] at hauth
  rw [ha456, ha480]
  have hdk := vecU8_expose A (stA + 456#64) s.uc.dk
  have hk464 : (stA + 456#64) + 8#64 = stA + 464#64 := by bv_omega
  have hk472 : (stA + 456#64) + 16#64 = stA + 472#64 := by bv_omega
  rw [hk464, hk472] at hdk
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono hauth (sepConj_mono_left hdk)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro k0
  apply Entails.sepExists_elim; intro k1
  apply Entails.sepExists_elim; intro k2
  apply Entails.sepExists_elim; intro a0
  apply Entails.sepExists_elim; intro a1
  apply Entails.sepExists_elim; intro a2
  apply Entails.sepExists_elim; intro a3
  apply Entails.sepExists_elim; intro a4
  apply Entails.sepExists_elim; intro a5
  refine Entails.sepExists_right a0 (Entails.sepExists_right a1
    (Entails.sepExists_right a2 (Entails.sepExists_right a3
      (Entails.sepExists_right a4 (Entails.sepExists_right a5
        (Entails.sepExists_right k0 (Entails.sepExists_right k1
          (Entails.sepExists_right k2 ?_))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Recombine `stA` cells after Arm 2 (`headerSent`) into `memRegion stA 928`. -/
theorem stA_headerSent_entails_928 (stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 : BitVec 64) :
    (stA ↦₆₄ 4#64) ∗
    memRegion (stA + 8#64) polyEncoderSize ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
     ((stA + 472#64) ↦₆₄ k2)) ∗
    memRegion (stA + 480#64) 408 ∗
    memRegion (stA + 888#64) 40 ⊢
    memRegion stA chunkedStatesSize := by
  have h8 : (stA ↦₆₄ 4#64) ⊢ memRegion stA 8 := by
    rw [ProofLib.memRegion_cells stA 1 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp]
    exact Entails.sepExists_right 4#64 (Entails.refl _)
  have h72 :
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
       ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
       ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
       ((stA + 472#64) ↦₆₄ k2)) ⊢
      memRegion (stA + 408#64) 72 := by
    rw [ProofLib.memRegion_cells (stA + 408#64) 9 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right k0 (Entails.sepExists_right k1
            (Entails.sepExists_right k2 (Entails.refl _)))))))))
  change _ ⊢ memRegion stA 928
  rw [ProofLib.memRegion_split' (b := stA) (n := 8) (k := 920)
        (b' := stA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := stA + 8#64) (n := 400) (k := 520)
        (b' := stA + 408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 408#64) (n := 72) (k := 448)
        (b' := stA + 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := stA + 480#64) (n := 408) (k := 40)
        (b' := stA + 888#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h8 (sepConj_mono_right (sepConj_mono_left h72))

/-- Assemble `outWords28` for Arm 2 (`headerSent`, tag `0x8000000000000002`) into
    `optProtoInnerStateAt A out (States.headerSent s).into_pb.innerState`. -/
theorem outWords28_entails_headerSent (A : RustAlloc) {F : ShaCompress}
    (out : BitVec 64)
    (k0 k1 k2 : BitVec 64)
    (a0 a1 a2 a3 a4 a5 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (w184 w192 w200 w208 w216 : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    outWords28 out
      0x8000000000000002#64
      k0 k1 k2 a0 a1 a2
      a3 a4 a5 s.uc.epoch e0 e1 e2 e3
      e4 e5 e6 d0 d1 d2 d3 d4
      w184 w192 w200 w208 w216 ∗
    protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
    protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
    authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
    vecU8Heap A k0 k1 k2 s.uc.dk ⊢
    optProtoInnerStateAt A out (States.headerSent s).into_pb.innerState := by
  dsimp only [States.into_pb, Chunked.SendEk.HeaderSent.into_pb,
    Unchunked.SendEk.EkSent.into_pb, spqrPolyApi, spqrAuthApi,
    optProtoInnerStateAt, protoInnerStateAt, protoChunkedHeaderSentAt,
    optProtoUnchunkedEkSentAt, protoUnchunkedEkSentAt,
    optProtoPolynomialEncoderAt, optProtoPolynomialDecoderAt, Option.map,
    pbToProtoPolyEncoder, protoPolyEncoderToPb,
    pbToProtoPolyDecoder, protoPolyDecoderToPb,
    optProtoAuthenticatorAt_some_into_pb]
  have hdk := vecU8_of_words_heap A (out + 8#64) k0 k1 k2 s.uc.dk
  have hk16 : (out + 8#64) + 8#64 = out + 16#64 := by bv_omega
  have hk24 : (out + 8#64) + 16#64 = out + 24#64 := by bv_omega
  rw [hk16, hk24] at hdk
  have hauth := authenticatorAt_of_words_heap A (out + 32#64) a0 a1 a2 a3 a4 a5 s.uc.auth
  have ha40 : (out + 32#64) + 8#64 = out + 40#64 := by bv_omega
  have ha48 : (out + 32#64) + 16#64 = out + 48#64 := by bv_omega
  have ha56 : (out + 32#64) + 24#64 = out + 56#64 := by bv_omega
  have ha64 : (out + 32#64) + 32#64 = out + 64#64 := by bv_omega
  have ha72 : (out + 32#64) + 40#64 = out + 72#64 := by bv_omega
  rw [ha40, ha48, ha56, ha64, ha72] at hauth
  have henc := protoPolynomialEncoder_of_words_heap A (out + 88#64)
    e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb
  have he96 : (out + 88#64) + 8#64 = out + 96#64 := by bv_omega
  have he104 : (out + 88#64) + 16#64 = out + 104#64 := by bv_omega
  have he112 : (out + 88#64) + 24#64 = out + 112#64 := by bv_omega
  have he120 : (out + 88#64) + 32#64 = out + 120#64 := by bv_omega
  have he128 : (out + 88#64) + 40#64 = out + 128#64 := by bv_omega
  have he136 : (out + 88#64) + 48#64 = out + 136#64 := by bv_omega
  rw [he96, he104, he112, he120, he128, he136] at henc
  have hdec := protoPolynomialDecoder_of_words_heap A (out + 144#64)
    d0 d1 d2 d3 d4 s.receiving_ct1.intoPb
  have hd152 : (out + 144#64) + 8#64 = out + 152#64 := by bv_omega
  have hd160 : (out + 144#64) + 16#64 = out + 160#64 := by bv_omega
  have hd168 : (out + 144#64) + 24#64 = out + 168#64 := by bv_omega
  have hd176 : (out + 144#64) + 32#64 = out + 176#64 := by bv_omega
  rw [hd152, hd160, hd168, hd176] at hdec
  have ho32 : (out + 8#64) + 24#64 = out + 32#64 := by bv_omega
  have ho80 : (out + 8#64) + 72#64 = out + 80#64 := by bv_omega
  have ho88 : (out + 8#64) + 80#64 = out + 88#64 := by bv_omega
  have ho144 : (out + 8#64) + 136#64 = out + 144#64 := by bv_omega
  rw [ho32, ho80, ho88, ho144]
  have h40 :
      ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
      ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
      ((out + 216#64) ↦₆₄ w216) ⊢
      memRegion (out + 184#64) 40 := by
    rw [ProofLib.memRegion_cells (out + 184#64) 5 (by decide)]
    simp only [ProofLib.cells_succ, ProofLib.cells_zero, sepConj_emp,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right w184 (Entails.sepExists_right w192
      (Entails.sepExists_right w200 (Entails.sepExists_right w208
        (Entails.sepExists_right w216 (Entails.refl _)))))
  unfold outWords28
  have hgroup :
      ((out ↦₆₄ 0x8000000000000002#64) ∗
       ((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗
       ((out + 24#64) ↦₆₄ k2) ∗ ((out + 32#64) ↦₆₄ a0) ∗
       ((out + 40#64) ↦₆₄ a1) ∗ ((out + 48#64) ↦₆₄ a2) ∗
       ((out + 56#64) ↦₆₄ a3) ∗ ((out + 64#64) ↦₆₄ a4) ∗
       ((out + 72#64) ↦₆₄ a5) ∗ ((out + 80#64) ↦₆₄ s.uc.epoch) ∗
       ((out + 88#64) ↦₆₄ e0) ∗ ((out + 96#64) ↦₆₄ e1) ∗
       ((out + 104#64) ↦₆₄ e2) ∗ ((out + 112#64) ↦₆₄ e3) ∗
       ((out + 120#64) ↦₆₄ e4) ∗ ((out + 128#64) ↦₆₄ e5) ∗
       ((out + 136#64) ↦₆₄ e6) ∗ ((out + 144#64) ↦₆₄ d0) ∗
       ((out + 152#64) ↦₆₄ d1) ∗ ((out + 160#64) ↦₆₄ d2) ∗
       ((out + 168#64) ↦₆₄ d3) ∗ ((out + 176#64) ↦₆₄ d4) ∗
       ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
      protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk =
      (out ↦₆₄ 0x8000000000000002#64) ∗
      (((((out + 8#64) ↦₆₄ k0) ∗ ((out + 16#64) ↦₆₄ k1) ∗
         ((out + 24#64) ↦₆₄ k2) ∗ vecU8Heap A k0 k1 k2 s.uc.dk) ∗
        (((out + 32#64) ↦₆₄ a0) ∗ ((out + 40#64) ↦₆₄ a1) ∗
         ((out + 48#64) ↦₆₄ a2) ∗ ((out + 56#64) ↦₆₄ a3) ∗
         ((out + 64#64) ↦₆₄ a4) ∗ ((out + 72#64) ↦₆₄ a5) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth) ∗
        ((out + 80#64) ↦₆₄ s.uc.epoch)) ∗
       (((out + 88#64) ↦₆₄ e0) ∗ ((out + 96#64) ↦₆₄ e1) ∗
        ((out + 104#64) ↦₆₄ e2) ∗ ((out + 112#64) ↦₆₄ e3) ∗
        ((out + 120#64) ↦₆₄ e4) ∗ ((out + 128#64) ↦₆₄ e5) ∗
        ((out + 136#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb) ∗
       (((out + 144#64) ↦₆₄ d0) ∗ ((out + 152#64) ↦₆₄ d1) ∗
        ((out + 160#64) ↦₆₄ d2) ∗ ((out + 168#64) ↦₆₄ d3) ∗
        ((out + 176#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb)) ∗
      (((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗
       ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
       ((out + 216#64) ↦₆₄ w216)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_right
    (sepConj_mono
      (sepConj_mono
        (sepConj_mono hdk (sepConj_mono_left hauth))
        (sepConj_mono henc hdec))
      h40)

/-! ## 2. Proof of Arm 2: `States.headerSent` (`+0 -> +60 -> +472 -> +500 -> +592 -> +604 -> +1544 -> ret`) -/

/-- Step 1 of Arm 2 (`+60 -> +96 -> +472 -> +496 -> memcpy`):
    dispatches on tag `4#64` (jump index `2` -> `+472`) and sets up `memcpy(s0.sp - 1360#64, stA + 8#64, 880)`. -/
theorem states_into_pb_headerSent_pre1
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
    (hx8 : s1.readReg64 .x8 = 4#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::into_pb" "memcpy")) s1
      (statesIntoPbJumpTableAt b ∗ Rest)
      (fun s2 P2 =>
        (P2 ⊢ statesIntoPbJumpTableAt b ∗ Rest) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 500#64 ∧
        s2.readReg64 .x0 = s0.sp - 1360#64 ∧
        s2.readReg64 .x1 = stA + 8#64 ∧
        (s2.readReg64 .x2).toNat = 880 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x28 = s0.sp - 256#64 ∧
        s2.readReg64 .x26 = s0.sp - 480#64 ∧
        s2.readReg64 .x22 = 0x8000000000000002#64 ∧
        s2.readReg64 .x21 = s0.sp - 1360#64 ∧
        s2.readReg64 .x20 = stA ∧
        s2.readReg64 .x19 = out ∧
        TraceCalleeSaved s2 s0) := by
  rcases htr1 with ⟨htr1, hvregs⟩
  have hadrp := fnAddr_adrp_5ce6c (H := Rust.withPanics ext) hb
  states_into_pb_fetches_range b (Rust.withPanics ext) 60 80
  states_into_pb_fetches_range b (Rust.withPanics ext) 472 28
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName,
    statesIntoPbJumpTableAt, statesIntoPbJumpTableBytes, BitVec.ofNat_eq_ofNat] at hadrp hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Step 2 of Arm 2 (`+500 -> +588 -> PolyEncoder::into_pb`):
    after `memcpy` returns to `+500`, reads `a0..a5, k0..k2` from `stA + 408..stA + 480`, stages
    them at `s0.sp - 256..s0.sp - 184` (using `s0.sp - 160..s0.sp - 112` as scratch), loads
    `s.uc.epoch` from `s0.sp - 888#64` into `x23`, and calls
    `<PolyEncoder>::into_pb(x0 = s0.sp - 400#64, x1 = stA + 8#64)`. -/
theorem states_into_pb_headerSent_pre2
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s2 : State) (out stA : BitVec 64)
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 epoch : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc2 : s2.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 500#64)
    (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 1520#64)
    (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hx28 : s2.readReg64 .x28 = s0.sp - 256#64)
    (hx26 : s2.readReg64 .x26 = s0.sp - 480#64)
    (hx22 : s2.readReg64 .x22 = 0x8000000000000002#64)
    (hx21 : s2.readReg64 .x21 = s0.sp - 1360#64)
    (hx20 : s2.readReg64 .x20 = stA)
    (hx19 : s2.readReg64 .x19 = out)
    (htr2 : TraceCalleeSaved s2 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 23100#64) s2
      (cells (s0.sp - 256#64) 9 ∗
       cells (s0.sp - 160#64) 6 ∗
       ((s0.sp - 888#64) ↦₆₄ epoch) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
        ((stA + 472#64) ↦₆₄ k2)) ∗
       Rest)
      (fun s3 P3 =>
        (P3 ⊢
          (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
           ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
           ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
           ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
           ((s0.sp - 192#64) ↦₆₄ a5)) ∗
          memRegion (s0.sp - 160#64) 48 ∗
          ((s0.sp - 888#64) ↦₆₄ epoch) ∗
          (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
           ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
           ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
           ((stA + 472#64) ↦₆₄ k2)) ∗
          Rest) ∧
        s3.sp = s0.sp - 1520#64 ∧
        s3.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 592#64 ∧
        s3.readReg64 .x0 = s0.sp - 400#64 ∧
        s3.readReg64 .x1 = stA + 8#64 ∧
        s3.readReg64 .x29 = s0.sp - 96#64 ∧
        s3.readReg64 .x26 = s0.sp - 480#64 ∧
        s3.readReg64 .x24 = s0.sp - 480#64 ∧
        s3.readReg64 .x23 = epoch ∧
        s3.readReg64 .x22 = 0x8000000000000002#64 ∧
        s3.readReg64 .x21 = s0.sp - 1360#64 ∧
        s3.readReg64 .x19 = out ∧
        TraceCalleeSaved s3 s0) := by
  rcases htr2 with ⟨htr2, hvregs⟩
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
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
    (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
     ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
     ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
     ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
     ((s0.sp - 192#64) ↦₆₄ a5)) ∗
    (((s0.sp - 160#64) ↦₆₄ a0) ∗ ((s0.sp - 152#64) ↦₆₄ a1) ∗
     ((s0.sp - 144#64) ↦₆₄ a2) ∗ ((s0.sp - 136#64) ↦₆₄ a3) ∗
     ((s0.sp - 128#64) ↦₆₄ a4) ∗ ((s0.sp - 120#64) ↦₆₄ a5)) ∗
    ((s0.sp - 888#64) ↦₆₄ epoch) ∗
    (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
     ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
     ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
     ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
     ((stA + 472#64) ↦₆₄ k2)) ∗
    Rest)
    (sepConj_mono_right (sepConj_mono_left hrejoin48)) ?_
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  repeat (apply SepWP.exists_elim; intro _)
  states_into_pb_fetches_range b (Rust.withPanics ext) 500 92
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  refine Drop.align_pre (by ac_rfl) ?_
  wp_done

/-- Step 3 of Arm 2 (`+592 -> +600 -> PolyDecoder::into_pb`):
    after `<PolyEncoder>::into_pb` returns to `+592`, sets `x0 = s0.sp - 344#64` (`x24 + 0x88`)
    and `x1 = s0.sp - 880#64` (`x21 + 0x1e0`) and calls `<PolyDecoder>::into_pb`. -/
theorem states_into_pb_headerSent_pre3
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s4 : State) (out epoch : BitVec 64)
    (hpc4 : s4.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 592#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = s0.sp - 1520#64)
    (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : s4.readReg64 .x26 = s0.sp - 480#64)
    (hx24 : s4.readReg64 .x24 = s0.sp - 480#64)
    (hx23 : s4.readReg64 .x23 = epoch)
    (hx22 : s4.readReg64 .x22 = 0x8000000000000002#64)
    (hx21 : s4.readReg64 .x21 = s0.sp - 1360#64)
    (hx19 : s4.readReg64 .x19 = out)
    (htr4 : TraceCalleeSaved s4 s0)
    (Rest : SepProp) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 25104#64) s4
      Rest
      (fun s5 P5 =>
        (P5 ⊢ Rest) ∧
        s5.sp = s0.sp - 1520#64 ∧
        s5.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 604#64 ∧
        s5.readReg64 .x0 = s0.sp - 344#64 ∧
        s5.readReg64 .x1 = s0.sp - 880#64 ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        s5.readReg64 .x26 = s0.sp - 480#64 ∧
        s5.readReg64 .x23 = epoch ∧
        s5.readReg64 .x22 = 0x8000000000000002#64 ∧
        s5.readReg64 .x19 = out ∧
        TraceCalleeSaved s5 s0) := by
  rcases htr4 with ⟨htr4, hvregs⟩
  states_into_pb_fetches_range b (Rust.withPanics ext) 592 12
  dsimp only [tripleRatchetProgAtExt, statesIntoPbName, BitVec.ofNat_eq_ofNat] at hpc4 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::into_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-- Step 4 of Arm 2 (`+604 -> +704 -> +1544 -> ret`):
    after `<PolyDecoder>::into_pb` returns to `+604`, copies `k0..k2, a0..a5, s.uc.epoch, e0..e6, d0..d4`
    into the epilogue staging slots and runs `states_into_pb_epilogue`. -/
theorem states_into_pb_headerSent_post (A : RustAlloc) (F : ShaCompress)
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 sf : State) (out stA : BitVec 64)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (a0 a1 a2 a3 a4 a5 k0 k1 k2 : BitVec 64)
    (e0 e1 e2 e3 e4 e5 e6 : BitVec 64)
    (d0 d1 d2 d3 d4 : BitVec 64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpcf : sf.pc = (tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName + 604#64)
    (hrunf : sf.status = .Running)
    (hspf : sf.sp = s0.sp - 1520#64)
    (hx29 : sf.readReg64 .x29 = s0.sp - 96#64)
    (hx26 : sf.readReg64 .x26 = s0.sp - 480#64)
    (hx23 : sf.readReg64 .x23 = s.uc.epoch)
    (hx22 : sf.readReg64 .x22 = 0x8000000000000002#64)
    (hx19 : sf.readReg64 .x19 = out)
    (htrf : TraceCalleeSaved sf s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) sf
      (cells (s0.sp - 1512#64) 19 ∗
       cells (s0.sp - 480#64) 10 ∗
       cells (s0.sp - 304#64) 6 ∗
       (((s0.sp - 344#64) ↦₆₄ d0) ∗ ((s0.sp - 336#64) ↦₆₄ d1) ∗
        ((s0.sp - 328#64) ↦₆₄ d2) ∗ ((s0.sp - 320#64) ↦₆₄ d3) ∗
        ((s0.sp - 312#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
        memRegion (s0.sp - 880#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
        ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
        ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
        ((s0.sp - 352#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 472 ∗
       ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 4#64) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
        ((stA + 472#64) ↦₆₄ k2)) ∗
       memRegion (stA + 480#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       memRegion (stA + 888#64) 40 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (StatesIntoPbPost A b s0 out stA (.headerSent s)) := by
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
       (((s0.sp - 344#64) ↦₆₄ d0) ∗ ((s0.sp - 336#64) ↦₆₄ d1) ∗
        ((s0.sp - 328#64) ↦₆₄ d2) ∗ ((s0.sp - 320#64) ↦₆₄ d3) ∗
        ((s0.sp - 312#64) ↦₆₄ d4) ∗
        protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
        memRegion (s0.sp - 880#64) polyDecoderSize ∗
        A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
       (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
        ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
        ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
        ((s0.sp - 352#64) ↦₆₄ e6) ∗
        protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
        memRegion (stA + 8#64) polyEncoderSize) ∗
       (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16 ∗
       ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 1360#64) 472 ∗
       ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
       statesIntoPbSavedCells s0 ∗
       (stA ↦₆₄ 4#64) ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
        ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
        ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
        ((stA + 472#64) ↦₆₄ k2)) ∗
       memRegion (stA + 480#64) 408 ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       memRegion (stA + 888#64) 40 ∗
       memRegion out optProtoInnerStateSize ∗
       statesIntoPbJumpTableAt b)
      (fun s2 P2 =>
        (P2 ⊢
          stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
          epilogueStagingCells s0.sp
            k0 k1 k2 a0 a1 a2
            a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
            0#64 w200 w208 w216 ∗
          memRegion (s0.sp - 1360#64) 880 ∗
          memRegion (s0.sp - 480#64) 176 ∗
          memRegion (s0.sp - 256#64) 160 ∗
          statesIntoPbSavedCells s0 ∗
          memRegion out optProtoInnerStateSize ∗
          (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
           protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
           authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
           vecU8Heap A k0 k1 k2 s.uc.dk ∗
           memRegion stA chunkedStatesSize ∗
           statesIntoPbJumpTableAt b ∗ A.pool)) ∧
        s2.sp = s0.sp - 1520#64 ∧
        s2.readReg64 .x29 = s0.sp - 96#64 ∧
        s2.readReg64 .x19 = out ∧
        s2.readReg64 .x22 = 0x8000000000000002#64 ∧
        s2.readReg64 .x21 = a3 ∧
        TraceCalleeSaved s2 s0) := by
    have hrejoin880 :
        memRegion (s0.sp - 1360#64) 472 ∗
        ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
        memRegion (s0.sp - 880#64) polyDecoderSize ⊢
        memRegion (s0.sp - 1360#64) 880 := by
      have h8 : ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ⊢ memRegion (s0.sp - 888#64) 8 := by
        rw [ProofLib.memRegion_cells (s0.sp - 888#64) 1 (by decide)]
        cells_unfold
        exact Entails.sepExists_right s.uc.epoch (Entails.refl _)
      rw [ProofLib.memRegion_split' (b := s0.sp - 1360#64) (n := 472) (k := 408)
            (b' := s0.sp - 888#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 888#64) (n := 8) (k := 400)
            (b' := s0.sp - 880#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_right (sepConj_mono_left h8)
    have hrejoin176 :
        ((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
        ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
        ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
        ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
        ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
        ((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
        ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
        ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
        ((s0.sp - 352#64) ↦₆₄ e6) ∗ ((s0.sp - 344#64) ↦₆₄ d0) ∗
        ((s0.sp - 336#64) ↦₆₄ d1) ∗ ((s0.sp - 328#64) ↦₆₄ d2) ∗
        ((s0.sp - 320#64) ↦₆₄ d3) ∗ ((s0.sp - 312#64) ↦₆₄ d4) ⊢
        memRegion (s0.sp - 480#64) 176 := by
      rw [ProofLib.memRegion_cells (s0.sp - 480#64) 22 (by decide)]
      cells_unfold
      exact Entails.sepExists_right k0 (Entails.sepExists_right k1
        (Entails.sepExists_right k2 (Entails.sepExists_right a0
          (Entails.sepExists_right a1 (Entails.sepExists_right a2
            (Entails.sepExists_right a3 (Entails.sepExists_right a4
              (Entails.sepExists_right a5 (Entails.sepExists_right s.uc.epoch
                (Entails.sepExists_right e0 (Entails.sepExists_right e1
                  (Entails.sepExists_right e2 (Entails.sepExists_right e3
                    (Entails.sepExists_right e4 (Entails.sepExists_right e5
                      (Entails.sepExists_right e6 (Entails.sepExists_right d0
                        (Entails.sepExists_right d1 (Entails.sepExists_right d2
                          (Entails.sepExists_right d3 (Entails.sepExists_right d4
                            (Entails.refl _))))))))))))))))))))))
    have hrejoin160 :
        (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
         ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
         ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
         ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
         ((s0.sp - 192#64) ↦₆₄ a5)) ∗
        memRegion (s0.sp - 184#64) 24 ∗
        memRegion (s0.sp - 160#64) 48 ∗
        memRegion (s0.sp - 112#64) 16 ⊢
        memRegion (s0.sp - 256#64) 160 := by
      have h72 :
          ((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
          ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
          ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
          ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
          ((s0.sp - 192#64) ↦₆₄ a5) ⊢
          memRegion (s0.sp - 256#64) 72 := by
        rw [ProofLib.memRegion_cells (s0.sp - 256#64) 9 (by decide)]
        cells_unfold
        exact Entails.sepExists_right k0 (Entails.sepExists_right k1
          (Entails.sepExists_right k2 (Entails.sepExists_right a0
            (Entails.sepExists_right a1 (Entails.sepExists_right a2
              (Entails.sepExists_right a3 (Entails.sepExists_right a4
                (Entails.sepExists_right a5 (Entails.refl _)))))))))
      rw [ProofLib.memRegion_split' (b := s0.sp - 256#64) (n := 72) (k := 88)
            (b' := s0.sp - 184#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 184#64) (n := 24) (k := 64)
            (b' := s0.sp - 160#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := s0.sp - 160#64) (n := 48) (k := 16)
            (b' := s0.sp - 112#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono_left h72
    have hstA := stA_headerSent_entails_928 stA a0 a1 a2 a3 a4 a5 k0 k1 k2
    refine SepWP.strengthen_entails_const (P₁ :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗
      epilogueStagingCells s0.sp
        k0 k1 k2 a0 a1 a2
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗
      (memRegion (s0.sp - 1360#64) 472 ∗
       ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
       memRegion (s0.sp - 880#64) polyDecoderSize) ∗
      (((s0.sp - 480#64) ↦₆₄ k0) ∗ ((s0.sp - 472#64) ↦₆₄ k1) ∗
       ((s0.sp - 464#64) ↦₆₄ k2) ∗ ((s0.sp - 456#64) ↦₆₄ a0) ∗
       ((s0.sp - 448#64) ↦₆₄ a1) ∗ ((s0.sp - 440#64) ↦₆₄ a2) ∗
       ((s0.sp - 432#64) ↦₆₄ a3) ∗ ((s0.sp - 424#64) ↦₆₄ a4) ∗
       ((s0.sp - 416#64) ↦₆₄ a5) ∗ ((s0.sp - 408#64) ↦₆₄ s.uc.epoch) ∗
       ((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗
       ((s0.sp - 384#64) ↦₆₄ e2) ∗ ((s0.sp - 376#64) ↦₆₄ e3) ∗
       ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
       ((s0.sp - 352#64) ↦₆₄ e6) ∗ ((s0.sp - 344#64) ↦₆₄ d0) ∗
       ((s0.sp - 336#64) ↦₆₄ d1) ∗ ((s0.sp - 328#64) ↦₆₄ d2) ∗
       ((s0.sp - 320#64) ↦₆₄ d3) ∗ ((s0.sp - 312#64) ↦₆₄ d4)) ∗
      ((((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗
        ((s0.sp - 240#64) ↦₆₄ k2) ∗ ((s0.sp - 232#64) ↦₆₄ a0) ∗
        ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
        ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗
        ((s0.sp - 192#64) ↦₆₄ a5)) ∗
       memRegion (s0.sp - 184#64) 24 ∗
       memRegion (s0.sp - 160#64) 48 ∗
       memRegion (s0.sp - 112#64) 16) ∗
      statesIntoPbSavedCells s0 ∗
      memRegion out optProtoInnerStateSize ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       ((stA ↦₆₄ 4#64) ∗
        memRegion (stA + 8#64) polyEncoderSize ∗
        (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗
         ((stA + 424#64) ↦₆₄ a2) ∗ ((stA + 432#64) ↦₆₄ a3) ∗
         ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
         ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗
         ((stA + 472#64) ↦₆₄ k2)) ∗
        memRegion (stA + 480#64) 408 ∗
        memRegion (stA + 888#64) 40) ∗
       statesIntoPbJumpTableAt b ∗ A.pool))
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hrejoin880
          (sepConj_mono hrejoin176
            (sepConj_mono hrejoin160
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left hstA)))))))))))) ?_
    states_into_pb_fetches_range b (Rust.withPanics ext) 604 104
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
    k0 k1 k2 a0 a1 a2
    a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
    0#64 w200 w208 w216
    (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
     protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
     vecU8Heap A k0 k1 k2 s.uc.dk ∗
     memRegion stA chunkedStatesSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc2 hrun2 hsp2 hx29_2 hx19_2 htr2
  rw [hx22_2, hx21_2] at hep
  unfold StatesIntoPbPost
  refine SepWP.strengthen_entails_const ?_ hep
  have hout := outWords28_entails_headerSent A out
    k0 k1 k2 a0 a1 a2 a3 a4 a5 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
    w184 0#64 w200 w208 w216 s
  have hgroup :
      outWords28 out 0x8000000000000002#64
        k0 k1 k2 a0 a1 a2 a3
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗
      stackAt s0.sp statesIntoPbStack ∗
      (protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk ∗
       memRegion stA chunkedStatesSize ∗
       statesIntoPbJumpTableAt b ∗ A.pool) =
      (outWords28 out 0x8000000000000002#64
        k0 k1 k2 a0 a1 a2 a3
        a4 a5 s.uc.epoch e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4 w184
        0#64 w200 w208 w216 ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       protoPolynomialDecoderHeap A d0 d1 d2 d3 d4 s.receiving_ct1.intoPb ∗
       authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
       vecU8Heap A k0 k1 k2 s.uc.dk) ∗
      memRegion stA chunkedStatesSize ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗
      stackAt s0.sp statesIntoPbStack := by ac_rfl
  rw [hgroup]
  exact sepConj_mono_left hout

/-- Stack split for Arm 2 (`headerSent`): splits `memRegion (sp0 - 1512#64) 1416` into the
    exact regions used across `memcpy`, `<PolyEncoder>::into_pb`, `<PolyDecoder>::into_pb`,
    and the epilogue. -/
theorem stack_1416_split_headerSent (sp0 : BitVec 64) :
    memRegion (sp0 - 1512#64) 1416 =
      cells (sp0 - 1512#64) 19 ∗
      memRegion (sp0 - 1360#64) 880 ∗
      cells (sp0 - 480#64) 10 ∗
      memRegion (sp0 - 400#64) protoPolynomialEncoderSize ∗
      memRegion (sp0 - 344#64) protoPolynomialDecoderSize ∗
      cells (sp0 - 304#64) 6 ∗
      cells (sp0 - 256#64) 9 ∗
      memRegion (sp0 - 184#64) 24 ∗
      cells (sp0 - 160#64) 6 ∗
      memRegion (sp0 - 112#64) 16 := by
  change memRegion (sp0 - 1512#64) 1416 =
    cells (sp0 - 1512#64) 19 ∗
    memRegion (sp0 - 1360#64) 880 ∗
    cells (sp0 - 480#64) 10 ∗
    memRegion (sp0 - 400#64) 56 ∗
    memRegion (sp0 - 344#64) 40 ∗
    cells (sp0 - 304#64) 6 ∗
    cells (sp0 - 256#64) 9 ∗
    memRegion (sp0 - 184#64) 24 ∗
    cells (sp0 - 160#64) 6 ∗
    memRegion (sp0 - 112#64) 16
  rw [ProofLib.memRegion_split' (b := sp0 - 1512#64) (n := 152) (k := 1264)
        (b' := sp0 - 1360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 1360#64) (n := 880) (k := 384)
        (b' := sp0 - 480#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 480#64) (n := 80) (k := 304)
        (b' := sp0 - 400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 400#64) (n := 56) (k := 248)
        (b' := sp0 - 344#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp0 - 344#64) (n := 40) (k := 208)
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
/-- Verifies `<States>::into_pb` on `.headerSent s` (Arm 2, tag `4`). -/
theorem states_into_pb_headerSent {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (henc : EncoderIntoPbOkExt b A ext)
    (hdec : DecoderIntoPbOkExt b A ext)
    (hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.headerSent s)) := by
  have henc_raw := sub_ok_encoderIntoPb_raw henc
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_raw hmemcpy
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  simp only [statesIntoPbVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hb⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.headerSent s) ∗
      statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp s0 s0 out stA (.headerSent s) _ R ?_
  refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_left
    (chunkedHeaderSent_expose A stA s))) ?_
  have hpull :
      memRegion out optProtoInnerStateSize ∗
        (∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
         ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
         ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
          (stA ↦₆₄ 4#64) ∗ polyEncoderAt A (stA + 8#64) s.sending_ek ∗
          (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
           ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
           ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
          (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
          authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
          vecU8Heap A k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40) ∗
        statesIntoPbJumpTableAt b ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
      ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64,
      ∃∗ a3 : BitVec 64, ∃∗ a4 : BitVec 64, ∃∗ a5 : BitVec 64,
      ∃∗ k0 : BitVec 64, ∃∗ k1 : BitVec 64, ∃∗ k2 : BitVec 64,
        stackAt s0.sp statesIntoPbStack ∗ (stA ↦₆₄ 4#64) ∗
        (polyEncoderAt A (stA + 8#64) s.sending_ek ∗
         (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
          ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
          ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
         (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
         authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
         vecU8Heap A k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
         memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b ∗ A.pool) := by
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat (apply Entails.sepExists_elim; intro _)
    rename_i a0 a1 a2 a3 a4 a5 k0 k1 k2
    refine Entails.sepExists_right a0 (Entails.sepExists_right a1
      (Entails.sepExists_right a2 (Entails.sepExists_right a3
        (Entails.sepExists_right a4 (Entails.sepExists_right a5
          (Entails.sepExists_right k0 (Entails.sepExists_right k1
            (Entails.sepExists_right k2 ?_))))))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWPp.weaken_pre hpull ?_
  refine SepWPp.exists_elim fun a0 => SepWPp.exists_elim fun a1 =>
    SepWPp.exists_elim fun a2 => SepWPp.exists_elim fun a3 =>
    SepWPp.exists_elim fun a4 => SepWPp.exists_elim fun a5 =>
    SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
    SepWPp.exists_elim fun k2 => ?_
  have hpro := states_into_pb_prologue_60 s0 out stA 4#64
    (polyEncoderAt A (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗ vecU8Heap A k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP hpro fun s1 hpc1 hrun1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_headerSent s0.sp]
  have hpre1 := states_into_pb_headerSent_pre1 s0 s1 out stA
    hb hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
    (stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ memRegion (s0.sp - 1360#64) 880 ∗
     cells (s0.sp - 480#64) 10 ∗ memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
     cells (s0.sp - 256#64) 9 ∗ memRegion (s0.sp - 184#64) 24 ∗
     cells (s0.sp - 160#64) 6 ∗ memRegion (s0.sp - 112#64) 16 ∗
     statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     polyEncoderAt A (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗ vecU8Heap A k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre1 fun s2 hpc2 hrun2
      ⟨hsp2, hlr2, hx0_2, hx1_2, hx2_2, hx29_2, hx28_2, hx26_2, hx22_2, hx21_2, hx20_2, hx19_2, htr2⟩ => ?_)
  have hfsp_align : ((s0.sp - 1520#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1520#64 hsp0_align (by decide)
  let F_enc_words : BitVec 64 → SepProp := fun a =>
    polyEncoderAt A a s.sending_ek ∗
    (((a + 400#64) ↦₆₄ a0) ∗ ((a + 408#64) ↦₆₄ a1) ∗ ((a + 416#64) ↦₆₄ a2) ∗
     ((a + 424#64) ↦₆₄ a3) ∗ ((a + 432#64) ↦₆₄ a4) ∗ ((a + 440#64) ↦₆₄ a5) ∗
     ((a + 448#64) ↦₆₄ k0) ∗ ((a + 456#64) ↦₆₄ k1) ∗ ((a + 464#64) ↦₆₄ k2))
  let G_dec : BitVec 64 → SepProp := fun a =>
    (a ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (a + 8#64) s.receiving_ct1
  have hF_src : F_enc_words (stA + 8#64) =
      (polyEncoderAt A (stA + 8#64) s.sending_ek ∗
       (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
        ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
        ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2))) := by
    dsimp only [F_enc_words]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_src : G_dec ((stA + 8#64) + 472#64) =
      (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) := by
    dsimp only [G_dec]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hG_dst : G_dec ((s0.sp - 1360#64) + 472#64) =
      (((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (s0.sp - 880#64) s.receiving_ct1) := by
    dsimp only [G_dec]
    simp only [arm64_norm]
  have hsrc_off : (stA + 8#64) + 472#64 = stA + 480#64 := by
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine call_memcpy_keep_relocate hmemcpy_raw
    (k := 472) (m := 408) (n := 880) (off := 472#64)
    (F := F_enc_words) (G := G_dec)
    rfl rfl
    (Relocatable.polyEncoder_words9 A s.sending_ek a0 a1 a2 a3 a4 a5 k0 k1 k2)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_ct1)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
      stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
      cells (s0.sp - 304#64) 6 ∗ cells (s0.sp - 256#64) 9 ∗
      memRegion (s0.sp - 184#64) 24 ∗ cells (s0.sp - 160#64) 6 ∗
      memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗ vecU8Heap A k0 k1 k2 s.uc.dk ∗
      memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
      statesIntoPbJumpTableAt b ∗ A.pool)
    hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx22_3 : s3.readReg64 .x22 = 0x8000000000000002#64 := hcs3.2.2.2.1.trans hx22_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_headerSent_pre2 s0 s3 out stA
    a0 a1 a2 a3 a4 a5 k0 k1 k2 s.uc.epoch
    hsp0_align hpc3 hrun3 hsp3 hx29_3 hx28_3 hx26_3 hx22_3 hx21_3 hx20_3 hx19_3 htr3
    (memRegion (s0.sp - 1360#64) 472 ∗ polyDecoderAt A (s0.sp - 880#64) s.receiving_ct1 ∗
     polyEncoderAt A (stA + 8#64) s.sending_ek ∗ memRegion (stA + 480#64) 408 ∗
     stackAt (s0.sp - 1520#64) encoderIntoPbStack ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
     cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
     memRegion (s0.sp - 400#64) protoPolynomialEncoderSize ∗
     memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗
     cells (s0.sp - 304#64) 6 ∗ memRegion (s0.sp - 184#64) 24 ∗
     memRegion (s0.sp - 112#64) 16 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗ vecU8Heap A k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTableAt b ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP hpre2 fun s4 hpc4 hrun4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx24_4, hx23_4, hx22_4, hx21_4, hx19_4, htr4⟩ => ?_)
  refine call_encoderIntoPb_expose henc_raw (s0.sp - 400#64) (stA + 8#64) s.sending_ek
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (s0.sp - 880#64) s.receiving_ct1 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b)
    hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun s5 e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hcs5 htr5 => ?_
  have hx19_5 : s5.readReg64 .x19 = out := hcs5.1.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = s0.sp - 1360#64 := hcs5.2.2.1.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = 0x8000000000000002#64 := hcs5.2.2.2.1.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = s.uc.epoch := hcs5.2.2.2.2.1.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = s0.sp - 480#64 := hcs5.2.2.2.2.2.1.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = s0.sp - 480#64 := hcs5.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_5 : s5.readReg64 .x29 = s0.sp - 96#64 := hcs5.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpre3 := states_into_pb_headerSent_pre3 s0 s5 out s.uc.epoch
    hpc5 hrun5 hsp5 hx29_5 hx26_5 hx24_5 hx23_5 hx22_5 hx21_5 hx19_5 htr5
    ((((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
      ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
      ((s0.sp - 352#64) ↦₆₄ e6) ∗
      protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
      memRegion (stA + 8#64) polyEncoderSize ∗
      A.pool ∗ stackAt (s0.sp - 1520#64) encoderIntoPbStack) ∗
     (cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗
      memRegion (s0.sp - 344#64) protoPolynomialDecoderSize ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      polyDecoderAt A (s0.sp - 880#64) s.receiving_ct1 ∗ statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b))
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]))
    (statesIntoPb_seq_sepWP hpre3 fun s6 hpc6 hrun6
      ⟨hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx26_6, hx23_6, hx22_6, hx19_6, htr6⟩ => ?_)
  refine call_decoderIntoPb_expose hdec_raw (s0.sp - 344#64) (s0.sp - 880#64) s.receiving_ct1
    (Frame :=
      cells (s0.sp - 1512#64) 19 ∗ cells (s0.sp - 480#64) 10 ∗ cells (s0.sp - 304#64) 6 ∗
      (((s0.sp - 400#64) ↦₆₄ e0) ∗ ((s0.sp - 392#64) ↦₆₄ e1) ∗ ((s0.sp - 384#64) ↦₆₄ e2) ∗
       ((s0.sp - 376#64) ↦₆₄ e3) ∗ ((s0.sp - 368#64) ↦₆₄ e4) ∗ ((s0.sp - 360#64) ↦₆₄ e5) ∗
       ((s0.sp - 352#64) ↦₆₄ e6) ∗
       protoPolynomialEncoderHeap A e0 e1 e2 e3 e4 e5 e6 s.sending_ek.intoPb ∗
       memRegion (stA + 8#64) polyEncoderSize) ∗
      (((s0.sp - 256#64) ↦₆₄ k0) ∗ ((s0.sp - 248#64) ↦₆₄ k1) ∗ ((s0.sp - 240#64) ↦₆₄ k2) ∗
       ((s0.sp - 232#64) ↦₆₄ a0) ∗ ((s0.sp - 224#64) ↦₆₄ a1) ∗ ((s0.sp - 216#64) ↦₆₄ a2) ∗
       ((s0.sp - 208#64) ↦₆₄ a3) ∗ ((s0.sp - 200#64) ↦₆₄ a4) ∗ ((s0.sp - 192#64) ↦₆₄ a5)) ∗
      memRegion (s0.sp - 184#64) 24 ∗ memRegion (s0.sp - 160#64) 48 ∗
      memRegion (s0.sp - 112#64) 16 ∗ ((s0.sp - 1520#64) ↦₆₄ 0#64) ∗
      memRegion (s0.sp - 1360#64) 472 ∗ ((s0.sp - 888#64) ↦₆₄ s.uc.epoch) ∗
      statesIntoPbSavedCells s0 ∗ (stA ↦₆₄ 4#64) ∗
      (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
       ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
       ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
      memRegion (stA + 480#64) 408 ∗ authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗
      vecU8Heap A k0 k1 k2 s.uc.dk ∗ memRegion (stA + 888#64) 40 ∗
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTableAt b)
    hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6
    (by ac_rfl)
    fun sf d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_6
  have hx22_f : sf.readReg64 .x22 = 0x8000000000000002#64 := hcsf.2.2.2.1.trans hx22_6
  have hx23_f : sf.readReg64 .x23 = s.uc.epoch := hcsf.2.2.2.2.1.trans hx23_6
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_6
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_headerSent_post A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 k0 k1 k2 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx23_f hx22_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
