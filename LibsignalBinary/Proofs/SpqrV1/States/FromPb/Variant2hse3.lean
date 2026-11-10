/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsd
import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Variant 2 (`HeaderSent`, `+508`) — Part E3

`receivingCt1` (`<PolyDecoder>::from_pb`) stage (`+9328..+9404`) and error exits to `+9228`.
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
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff libsignalSessionCode
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append

attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  fnOff_drop_poly16
  fnOff_drop_proto_poly_encoder
  fnOff_drop_poly_encoder_local2
  fnOff_drop_ek_sent
  fnOff_poly_encoder_from_pb
  fnOff_poly_decoder_from_pb
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_bv_add_add_lit (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_x23_add_193_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (193#64).signExtend 64 = fsp + 1041#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v2hse3_x25_add_65_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (65#64).signExtend 64 = fsp + 1857#64 := by bv_kernel

/-! ## `receivingCt1 = none` Branch (`+9328 -> +11024 -> +9228`) -/

/-- At `+9328` (`0x5c514: b.eq 0x5cbb4`), when `s1.pstate = addsPState64 noneCap 1#64`
(`receivingCt1 = none`), takes `b.eq +11024`, drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hse3_none_dec_9328_to_9228
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        ((fsp + 200#64) ↦₆₄ ca1) ∗
        ((fsp + 1272#64) ↦₆₄ pa1) ∗
        ((fsp + 232#64) ↦₆₄ ca2) ∗
        ((fsp + 184#64) ↦₆₄ pa2) ∗
        ((fsp + 176#64) ↦₆₄ pa3) ∗
        vecCapPtrDealloc A ca1 pa1 ∗
        vecCapPtrDealloc A ca2 pa2 ∗
        vecCapPtrDealloc A ca3 pa3 ∗
        A.pool ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1392#64) 400 ∗
          ((fsp + 200#64) ↦₆₄ ca1) ∗
          ((fsp + 1272#64) ↦₆₄ pa1) ∗
          ((fsp + 232#64) ↦₆₄ ca2) ∗
          ((fsp + 184#64) ↦₆₄ pa2) ∗
          ((fsp + 176#64) ↦₆₄ pa3) ∗
          A.pool ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11024#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      ((fsp + 200#64) ↦₆₄ ca1) ∗
      ((fsp + 1272#64) ↦₆₄ pa1) ∗
      ((fsp + 232#64) ↦₆₄ ca2) ∗
      ((fsp + 184#64) ↦₆₄ pa2) ∗
      ((fsp + 176#64) ↦₆₄ pa3) ∗
      vecCapPtrDealloc A ca1 pa1 ∗
      vecCapPtrDealloc A ca2 pa2 ∗
      vecCapPtrDealloc A ca3 pa3 ∗
      A.pool ∗ Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x23 = fsp + 1392#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9328 4
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx23_2, hx26_2, htr2⟩
    exact v2hsd_cleanup_11024_to_9228 hA s0 s2 fsp out ca1 pa1 ca2 pa2 ca3 pa3 enc Frame
      hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 htr2

/-! ## Copy `ProtoPolynomialDecoder` (`+9328 -> +9384`) and Call `<PolyDecoder>::from_pb` (`+9384 -> +35448`) -/

theorem v2hse3_byte_pointsTo64_eq_pointsTo64_byte (a w : BitVec 64) (b : BitVec 8) :
    (a ↦₆₄ w) ∗ ((a + 8#64) ↦₈ b) =
      (a ↦₈ EncoderFromPb.loByte w) ∗ ((a + 1#64) ↦₆₄ EncoderFromPb.unshiftWord w b) := by
  rw [ProofLib.pointsTo64_eq_pointsToBytes a w,
      ProofLib.pointsTo64_eq_pointsToBytes (a + 1#64),
      ← ProofLib.pointsToBytes_cons,
      EncoderFromPb.loByte_cons_unpack64_unshiftWord w b,
      ProofLib.pointsToBytes_append a (unpack64 w) [b], unpack64_length]
  simp only [ProofLib.pointsToBytes_cons, ProofLib.pointsToBytes_nil, sepConj_emp]

theorem v2hse3_triple64_to_byte_qword_tail7 (a w8 w16 w24 : BitVec 64) :
    (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ w24) =
      (a ↦₈ EncoderFromPb.loByte w8) ∗
      ((a + 1#64) ↦₁₂₈
        (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
         EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
      ((a + 17#64) ↦ₛ EncoderFromPb.hiBytes7 w24) := by
  have hp := EncoderFromPb.pair64_to_byte_word_tail7 (a + 8#64) w16 w24
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
  have ha17 : a + 8#64 + 9#64 = a + 17#64 := by bv_omega
  rw [ha16, ha9, ha17] at hp
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9' : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9'] at hq
  rw [hp, ← sepConj_assoc, ← sepConj_assoc,
      v2hse3_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8),
      sepConj_assoc (a ↦₈ EncoderFromPb.loByte w8), hq]

theorem v2hse3_byte_qword_mem7_to_triple64 (a w8 w16 w24 : BitVec 64) :
    (a ↦₈ EncoderFromPb.loByte w8) ∗
    ((a + 1#64) ↦₁₂₈
      (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
       EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))) ∗
    memRegion (a + 17#64) 7 ⊢
    ∃∗ u16 : BitVec 64,
      (a ↦₆₄ w8) ∗ ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₆₄ u16) := by
  have hq := EncoderFromPb.pointsTo64_pair_eq_pointsTo128 (a + 1#64)
    (EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16))
    (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24))
  have ha9 : a + 1#64 + 8#64 = a + 9#64 := by bv_omega
  rw [ha9] at hq
  rw [← hq, ← sepConj_assoc, ← sepConj_assoc,
      ← v2hse3_byte_pointsTo64_eq_pointsTo64_byte a w8 (EncoderFromPb.loByte w16),
      sepConj_assoc, sepConj_assoc]
  have hjoin : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
      (((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
       memRegion (a + 17#64) 7) ⊢
      ((a + 8#64) ↦₆₄ w16) ∗ (∃∗ u16 : BitVec 64, (a + 16#64) ↦₆₄ u16) := by
    have hb : ((a + 8#64) ↦₈ EncoderFromPb.loByte w16) ∗
        ((a + 9#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) =
        ((a + 8#64) ↦₆₄ w16) ∗ ((a + 16#64) ↦₈ EncoderFromPb.loByte w24) := by
      have h := (v2hse3_byte_pointsTo64_eq_pointsTo64_byte (a + 8#64) w16 (EncoderFromPb.loByte w24)).symm
      have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
      have ha9' : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
      rw [ha16, ha9'] at h
      exact h
    rw [← sepConj_assoc, hb, sepConj_assoc]
    refine sepConj_mono_right ?_
    have hm : memRegion (a + 16#64) 1 ∗ memRegion (a + 17#64) 7 = memRegion (a + 16#64) 8 := by
      rw [← ProofLib.memRegion_split' (b := a + 16#64) (n := 1) (k := 7)
        (b' := a + 17#64) rfl (by bv_omega) (by decide)]
    rw [← ProofLib.memRegion_eight (a + 16#64), ← hm]
    exact sepConj_mono_left (pointsTo8_entails_memRegion _ _)
  refine Entails.trans (sepConj_mono_right hjoin) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right]
  exact Entails.refl _

theorem v2hse3_memRegion_1848_split_decCopy (fsp : BitVec 64) :
    memRegion (fsp + 1848#64) 40 ⊢
      (∃∗ z0 : BitVec 64, (fsp + 1848#64) ↦₆₄ z0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 1856#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 1857#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 1865#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1873#64) 7 ∗
      (∃∗ z32 : BitVec 64, (fsp + 1880#64) ↦₆₄ z32) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    mem64_entails _

theorem v2hse3_fsp1040_to_step9332 (fsp d8 d16 d24 d32 : BitVec 64) :
    ((fsp + 1040#64) ↦₆₄ d8) ∗
    ((fsp + 1048#64) ↦₆₄ d16) ∗
    ((fsp + 1056#64) ↦₆₄ d24) ∗
    ((fsp + 1064#64) ↦₆₄ d32) ⊢
      ((fsp + 1040#64) ↦₈ EncoderFromPb.loByte d8) ∗
      ((fsp + 1041#64) ↦₆₄ EncoderFromPb.unshiftWord d8 (EncoderFromPb.loByte d16)) ∗
      ((fsp + 1049#64) ↦₆₄ EncoderFromPb.unshiftWord d16 (EncoderFromPb.loByte d24)) ∗
      ((fsp + 1057#64) ↦ₛ EncoderFromPb.hiBytes7 d24) ∗
      ((fsp + 1064#64) ↦₆₄ d32) := by
  have htri := v2hse3_triple64_to_byte_qword_tail7 (fsp + 1040#64) d8 d16 d24
  simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
    v2hse3_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc] at htri
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1040#64) ↦₆₄ d8) ∗ ((fsp + 1048#64) ↦₆₄ d16) ∗ ((fsp + 1056#64) ↦₆₄ d24)) ∗
    ((fsp + 1064#64) ↦₆₄ d32) by ac_rfl)) ?_
  rw [htri]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- At `+9328` when `s1.pstate = addsPState64 d0 1#64` with `hd0 : d0.toNat < 2 ^ 63`,
falls through `b.eq +11024` and copies `(d0, d8, d16, d24, d32)` from `x22` and `fsp + 1040..1064`
into `fsp + 1848..1888`, reaching `+9384` with `x0 = fsp + 1888#64`, `x1 = fsp + 1848#64`,
`x19 = out`, `x20 = x20_val`, `x21 = x21_val`, `x22 = fsp + 1888#64`, `x23 = fsp + 848#64`,
`x25 = fsp + 1792#64`, `x26 = ca3`, `x28 = x28_val`. -/
theorem v2hse3_copy_dec_9328_to_9384
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hd0 : d0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = d0)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (hpstate1 : s1.pstate = addsPState64 d0 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9384#64) s1
      (((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ d16) ∗
        ((fsp + 1056#64) ↦₆₄ d24) ∗
        ((fsp + 1064#64) ↦₆₄ d32) ∗
        memRegion (fsp + 1848#64) 40 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1040#64) ↦₆₄ d8) ∗
          ((fsp + 1048#64) ↦₆₄ d16) ∗
          ((fsp + 1056#64) ↦₆₄ d24) ∗
          ((fsp + 1064#64) ↦₆₄ d32) ∗
          ((fsp + 1848#64) ↦₆₄ d0) ∗
          ((fsp + 1856#64) ↦₆₄ d8) ∗
          ((fsp + 1864#64) ↦₆₄ d16) ∗
          ((fsp + 1872#64) ↦₆₄ d24) ∗
          ((fsp + 1880#64) ↦₆₄ d32) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hdec_ne := cap_add_one_beq_zero_false hd0
  refine SepWP.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      (((fsp + 1040#64) ↦₆₄ d8) ∗
       ((fsp + 1048#64) ↦₆₄ d16) ∗
       ((fsp + 1056#64) ↦₆₄ d24) ∗
       ((fsp + 1064#64) ↦₆₄ d32)) ∗
      memRegion (fsp + 1848#64) 40 ∗
      Frame by ac_rfl))
      (sepConj_mono (v2hse3_fsp1040_to_step9332 fsp d8 d16 d24 d32)
        (sepConj_mono_left (v2hse3_memRegion_1848_split_decCopy fsp)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro z32
  apply ProofLib.SepWP.exists_left; intro q9_hi
  apply ProofLib.SepWP.exists_left; intro q9_lo
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro z0
  states_from_pb_fetches_range b (Rust.withPanics ext) 9328 56
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 9348#64)
    (P_mid :=
      ((fsp + 1040#64) ↦₆₄ d8) ∗
      ((fsp + 1048#64) ↦₆₄ d16) ∗
      ((fsp + 1056#64) ↦₆₄ d24) ∗
      ((fsp + 1064#64) ↦₆₄ d32) ∗
      ((fsp + 1848#64) ↦₆₄ z0) ∗
      ((fsp + 1856#64) ↦₈ b8) ∗
      ((fsp + 1857#64) ↦₆₄ q9_lo) ∗
      ((fsp + 1865#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1873#64) 7 ∗
      ((fsp + 1880#64) ↦₆₄ z32) ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = (EncoderFromPb.loByte d8).zeroExtend 64 ∧
      sm.readReg64 .x9 = d32 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = x20_val ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = d0 ∧
      sm.readReg64 .x23 = fsp + 848#64 ∧
      sm.readReg64 .x25 = fsp + 1792#64 ∧
      sm.readReg64 .x26 = ca3 ∧
      sm.readReg64 .x28 = x28_val ∧
      sm.readVReg128 0#5 = (EncoderFromPb.unshiftWord d16 (EncoderFromPb.loByte d24) ++
        EncoderFromPb.unshiftWord d8 (EncoderFromPb.loByte d16)) ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htri_fsp := (v2hse3_triple64_to_byte_qword_tail7 (fsp + 1040#64) d8 d16 d24).symm
      simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
        v2hse3_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc] at htri_fsp
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1040#64) ↦₈ EncoderFromPb.loByte d8) ∗
         ((fsp + 1041#64) ↦₆₄ EncoderFromPb.unshiftWord d8 (EncoderFromPb.loByte d16)) ∗
         ((fsp + 1049#64) ↦₆₄ EncoderFromPb.unshiftWord d16 (EncoderFromPb.loByte d24)) ∗
         ((fsp + 1057#64) ↦ₛ EncoderFromPb.hiBytes7 d24)) ∗
        (((fsp + 1064#64) ↦₆₄ d32) ∗
         ((fsp + 1848#64) ↦₆₄ z0) ∗
         ((fsp + 1856#64) ↦₈ b8) ∗
         ((fsp + 1857#64) ↦₆₄ q9_lo) ∗
         ((fsp + 1865#64) ↦₆₄ q9_hi) ∗
         memRegion (fsp + 1873#64) 7 ∗
         ((fsp + 1880#64) ↦₆₄ z32) ∗
         Frame) by ac_rfl)) ?_
      rw [htri_fsp]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx25_2, hx26_2, hx28_2, hq0_2, htr2⟩
    refine EncoderFromPb.seq_clean (mid := entry + 9376#64)
      (P_mid :=
        (∃∗ u16 : BitVec 64,
          ((fsp + 1856#64) ↦₆₄ d8) ∗
          ((fsp + 1864#64) ↦₆₄ d16) ∗
          ((fsp + 1872#64) ↦₆₄ u16)) ∗
        ((fsp + 1040#64) ↦₆₄ d8) ∗
        ((fsp + 1048#64) ↦₆₄ d16) ∗
        ((fsp + 1056#64) ↦₆₄ d24) ∗
        ((fsp + 1064#64) ↦₆₄ d32) ∗
        ((fsp + 1848#64) ↦₆₄ d0) ∗
        ((fsp + 1880#64) ↦₆₄ z32) ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x8 = d24 ∧
        sm.readReg64 .x9 = d32 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hfsp_q := v2hse3_byte_qword_mem7_to_triple64 (fsp + 1856#64) d8 d16 d24
        simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
          v2hse3_bv_add_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc] at hfsp_q
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 1856#64) ↦₈ EncoderFromPb.loByte d8) ∗
           ((fsp + 1857#64) ↦₆₄ EncoderFromPb.unshiftWord d8 (EncoderFromPb.loByte d16)) ∗
           ((fsp + 1865#64) ↦₆₄ EncoderFromPb.unshiftWord d16 (EncoderFromPb.loByte d24)) ∗
           memRegion (fsp + 1873#64) 7) ∗
          (((fsp + 1040#64) ↦₆₄ d8) ∗
           ((fsp + 1048#64) ↦₆₄ d16) ∗
           ((fsp + 1056#64) ↦₆₄ d24) ∗
           ((fsp + 1064#64) ↦₆₄ d32) ∗
           ((fsp + 1848#64) ↦₆₄ d0) ∗
           ((fsp + 1880#64) ↦₆₄ z32) ∗
           Frame) by ac_rfl)) ?_
        exact sepConj_mono_left hfsp_q
      · wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx28_3, htr3⟩
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro u16
      wp_steps
      refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
      wp_done

/-- Execute `bl 0x62b1c` at `+9384` to `<PolyDecoder>::from_pb` entry (`+35448`),
setting `x30 = entry + 9388#64`. -/
theorem v2hse3_bl_decoder_9384_to_35448
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9384#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 35448#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9388#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 9384 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## `<PolyDecoder>::from_pb` Return Branches (`+9388 -> +9228` on `Err`, `+9388 -> +9404` on `Ok`) -/

theorem v2hse3_resultPolyDecoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ noneCap) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyDecoderFromPbAt,
    resultPolyDecoderErrByteOff, resultPolyDecoderErrTailSize, noneCap]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

theorem v2hse3_1888_tag_392_to_memRegion_400 (fsp tag : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 1896#64) 392 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
        (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-- At `+9388`, when `resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err)` holds,
loads `noneCap` from `[sp, #0x760]`, stores `noneCap` to `[sp, #0xd8]` (`fsp + 216#64`),
takes `b.eq +11240`, drops `enc` at `fsp + 1392` and `uc` at `fsp + 1264` via
`v2hsd_cleanup_11240_to_9228`, and reaches `+9228` with `x23 = 0#64`. -/
theorem v2hse3_err_dec_9388_to_9228
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (fsp out w216_old : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (err : PolynomialError) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9228#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        polyEncoderAt A (fsp + 1392#64) enc ∗
        unchunkedEkSentAt A (fsp + 1264#64) uc ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          ((fsp + 216#64) ↦₆₄ noneCap) ∗
          memRegion (fsp + 1392#64) 400 ∗
          memRegion (fsp + 1264#64) 80 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x23 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v2hse3_resultPolyDecoder_err_entails_tag_392 A fsp err))) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 11240#64)
    (P_mid :=
      stackAt fsp encoderFromPbStack ∗
      polyEncoderAt A (fsp + 1392#64) enc ∗
      unchunkedEkSentAt A (fsp + 1264#64) uc ∗
      A.pool ∗
      (memRegion (fsp + 1888#64) 400 ∗
       ((fsp + 216#64) ↦₆₄ noneCap) ∗
       Frame))
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 9388 16
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hm400 := v2hse3_1888_tag_392_to_memRegion_400 fsp 18446744073709551615#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((fsp + 1888#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion (fsp + 1896#64) 392) ∗
        (stackAt fsp encoderFromPbStack ∗
         polyEncoderAt A (fsp + 1392#64) enc ∗
         unchunkedEkSentAt A (fsp + 1264#64) uc ∗
         A.pool ∗
         (((fsp + 216#64) ↦₆₄ 18446744073709551615#64) ∗ Frame)) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm400) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, htr2⟩
    have h11240 := v2hsd_cleanup_11240_to_9228 hA s0 s2 fsp out enc uc
      (memRegion (fsp + 1888#64) 400 ∗ ((fsp + 216#64) ↦₆₄ noneCap) ∗ Frame)
      hfsp_align hpc2 hrun2 hsp2 hx19_2 htr2
    exact SepWP.mono h11240 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- At `+9388`, when `((fsp + 1888#64) ↦₆₄ dw0)` holds with `hdw0 : dw0.toNat < 2 ^ 63`,
loads `dw0` from `[sp, #0x760]`, stores `dw0` to `[sp, #0xd8]` (`fsp + 216#64`),
falls through `b.eq +11240`, and reaches `+9404` preserving `x19`, `x20`, `x21`, `x22`,
`x23`, `x25`, `x26`, `x28`. -/
theorem v2hse3_ok_dec_9388_to_9404
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val dw0 w216_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdw0 : dw0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = x20_val)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hx28_1 : s1.readReg64 .x28 = x28_val)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 9404#64) s1
      (((fsp + 1888#64) ↦₆₄ dw0) ∗
        ((fsp + 216#64) ↦₆₄ w216_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 1888#64) ↦₆₄ dw0) ∗
          ((fsp + 216#64) ↦₆₄ dw0) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x8 = dw0 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = x20_val ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = ca3 ∧
        sm.readReg64 .x28 = x28_val ∧
        TraceCalleeSaved sm s0) := by
  have hdw0_ne := cap_add_one_beq_zero_false hdw0
  states_from_pb_fetches_range b (Rust.withPanics ext) 9388 16
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

end CryptoVerification.SpqrV1.States.FromPb
