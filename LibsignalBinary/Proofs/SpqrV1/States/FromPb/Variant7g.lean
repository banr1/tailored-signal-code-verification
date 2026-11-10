/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Epilogue
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# SPQR V1 `<States>::from_pb`: Variant 7 (`Ct1Sampled`, `+1056`) — Part G

Covers the `s.sendingCt1 = none` cleanup path (`+3552 -> +7100 -> +4632`), `<PolyEncoder>::from_pb`
56-byte copy and call (`+3652 -> +3716 -> +32996`), and `<PolyEncoder>::from_pb = Err` cleanup
(`+3720 -> +3732 -> +4632`).
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
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  statesFromPb_fnOff
  stubOff_rust_no_alloc_shim
  stubOff_rust_alloc
  stubOff_rust_dealloc
  stubOff_memcpy
  stubOff_handle_error

/-! ## 1. `s.sendingCt1 = none` Path (`+3552 -> +7100 -> +4632`) -/

/-- When `<Ct1Sent>::from_pb` returns `Ok(uc)` at `fsp + 1888..2016` and `[pbA + 128] = noneCap`
(`s.sendingCt1 = none`), spills `uc` to `fsp + 1264..1392`, branches to `+7100`, deallocates
all 5 vectors of `uc` and `optDec`, and reaches `+4632`. -/
theorem v7_uc_ok_none_enc_3552_to_4632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        ct1SentAt A (F := F) ((s0.sp - 2400#64) + 1888#64) uc ∗
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
        ((pbA + 128#64) ↦₆₄ noneCap) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          ((pbA + 128#64) ↦₆₄ noneCap) ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v7_ct1SentAt_unpack A (F := F) ((s0.sp - 2400#64) + 1888#64) uc))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro c1
  apply ProofLib.SepWP.exists_left; intro p1
  apply ProofLib.SepWP.exists_left; intro l1
  apply ProofLib.SepWP.exists_left; intro c2
  apply ProofLib.SepWP.exists_left; intro p2
  apply ProofLib.SepWP.exists_left; intro l2
  apply ProofLib.SepWP.exists_left; intro c3
  apply ProofLib.SepWP.exists_left; intro p3
  apply ProofLib.SepWP.exists_left; intro l3
  apply ProofLib.SepWP.exists_left; intro c4
  apply ProofLib.SepWP.exists_left; intro p4
  apply ProofLib.SepWP.exists_left; intro l4
  apply ProofLib.SepWP.exists_left; intro c5
  apply ProofLib.SepWP.exists_left; intro p5
  apply ProofLib.SepWP.exists_left; intro l5
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
    (⌜c1.toNat < 2 ^ 63⌝ ∗
     (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
      ((pbA + 128#64) ↦₆₄ noneCap) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       A.pool ∗ Frame))) by ac_rfl))
    (sepConj_mono_left (v7_ct1SentHeap_entails_dealloc A uc
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5))) ?_
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗
    (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1888#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
     memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
     ((pbA + 128#64) ↦₆₄ noneCap) ∗
     (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      (vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5) ∗
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
       v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
      A.pool ∗ Frame)) by ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hc1
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 7100#64)
    (P_mid :=
      memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      ((pbA + 128#64) ↦₆₄ noneCap) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5) ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       A.pool ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x1 = c1 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = p1 ∧
      TraceCalleeSaved sm s0)
    (v7_uc_ok_spill_3552_to_7100 s0 s1 (s0.sp - 2400#64) out pbA cap_dec
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch _
      hfsp_align hc1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
  rw [v7_ct1SentWordsAt_1264_eq_spill_other]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (v7_cleanup_7100 hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec
        (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
         memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
         ((pbA + 128#64) ↦₆₄ noneCap) ∗ Frame)
        hcap_dec hsp0_align hpc2 hrun2 hsp2 hx1_2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2) ?_)
  intro s3 P3 hrun3 hpc3 ⟨hP3, hq⟩
  refine ⟨Entails.trans hP3 ?_, hq⟩
  have h1264 :
      v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
      v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ⊢
      memRegion ((s0.sp - 2400#64) + 1264#64) 128 := by
    rw [← v7_ct1SentWordsAt_1264_eq_spill_other]
    exact v7_ct1SentWordsAt_entails_128 ((s0.sp - 2400#64) + 1264#64)
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
  refine Entails.trans (Entails.of_eq (show _ =
    (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
     v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     memRegion ((s0.sp - 2400#64) + 1888#64) 128 ∗
     ((pbA + 128#64) ↦₆₄ noneCap) ∗
     memRegion (pbA + 184#64) 40 ∗
     A.pool ∗
     Frame) by ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by ac_rfl))

/-! ## 2. `<PolyEncoder>::from_pb` Copy (`+3652 -> +3716`) and Call (`+3716 -> +32996`) -/

theorem v7_memRegion_1792_split_encCopy (fsp : BitVec 64) :
    memRegion (fsp + 1792#64) 56 ⊢
      (∃∗ d0 : BitVec 64, (fsp + 1792#64) ↦₆₄ d0) ∗
      (∃∗ b8 : BitVec 8, (fsp + 1800#64) ↦₈ b8) ∗
      (∃∗ q9_lo : BitVec 64, (fsp + 1801#64) ↦₆₄ q9_lo) ∗
      (∃∗ q9_hi : BitVec 64, (fsp + 1809#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1817#64) 7 ∗
      (∃∗ d32 : BitVec 64, (fsp + 1824#64) ↦₆₄ d32) ∗
      (∃∗ d40 : BitVec 64, (fsp + 1832#64) ↦₆₄ d40) ∗
      (∃∗ d48 : BitVec 64, (fsp + 1840#64) ↦₆₄ d48) := by
  exact split_top <|
    split_step (mem64_entails _) <|
    split_step (mem8_entails _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    split_step (Entails.refl _) <|
    split_step (mem64_entails _) <|
    split_step (mem64_entails _) <|
    mem64_entails _

theorem v7_encTailWordsAt_to_step3652
    (pbA w8 w16 w24 w32 w40 w48 : BitVec 64) :
    v7_encTailWordsAt (pbA + 128#64) w8 w16 w24 w32 w40 w48 ⊢
      ((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
      ((pbA + 137#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
      ((pbA + 144#64) ↦₆₄ w16) ∗
      ((pbA + 152#64) ↦₆₄ w24) ∗
      ((pbA + 160#64) ↦₆₄ w32) ∗
      ((pbA + 168#64) ↦₆₄ w40) ∗
      ((pbA + 176#64) ↦₆₄ w48) := by
  unfold v7_encTailWordsAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h8 := pointsTo64_split_1_7 (pbA + 136#64) w8
  have ha9 : pbA + 136#64 + 1#64 = pbA + 137#64 := by bv_omega
  rw [ha9] at h8
  rw [h8]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
/-- Copy `ProtoPolynomialEncoder` (`56`B) from `pbA + 128` to `fsp + 1792` (`sp + 0x700`),
store `c1` (`x1`) to `[sp, #0x18]`, and set `x0 = fsp + 1888`, `x1 = fsp + 1792`,
`x20 = fsp + 1792`, `x25 = fsp + 1888` at `+3652 -> +3716`. -/
theorem v7_copy_enc_3652_to_3716
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old : BitVec 64)
    (encPb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3652#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = c1)
    (hx8_1 : s1.readReg64 .x8 = cap_enc)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1792#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3716#64) s1
      (((pbA + 128#64) ↦₆₄ cap_enc) ∗
        v7_optProtoPolyEncoderTail A (pbA + 128#64) cap_enc (some encPb) ∗
        memRegion (fsp + 1792#64) 56 ∗
        ((fsp + 24#64) ↦₆₄ slot24_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 128#64) 56 ∗
          protoPolynomialEncoderAt A (fsp + 1792#64) encPb ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        TraceCalleeSaved sm s0) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_encTail_unpack A (pbA + 128#64) cap_enc encPb)
      (sepConj_mono_left (v7_memRegion_1792_split_encCopy fsp)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d48
  apply ProofLib.SepWP.exists_left; intro d40
  apply ProofLib.SepWP.exists_left; intro d32
  apply ProofLib.SepWP.exists_left; intro q9_hi
  apply ProofLib.SepWP.exists_left; intro q9_lo
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro w32
  apply ProofLib.SepWP.exists_left; intro w40
  apply ProofLib.SepWP.exists_left; intro w48
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v7_encTailWordsAt_to_step3652 pbA w8 w16 w24 w32 w40 w48))) ?_
  states_from_pb_fetches_range b (Rust.withPanics ext) 3652 64
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  refine EncoderFromPb.seq_clean (mid := entry + 3680#64)
    (P_mid :=
      ((pbA + 128#64) ↦₆₄ cap_enc) ∗
      (((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
       ((pbA + 137#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
       ((pbA + 145#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
       ((pbA + 153#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
      (((pbA + 160#64) ↦₆₄ w32) ∗
       ((pbA + 168#64) ↦₆₄ w40) ∗
       ((pbA + 176#64) ↦₆₄ w48)) ∗
      v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
      ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
      ((fsp + 1800#64) ↦₈ b8) ∗
      ((fsp + 1801#64) ↦₆₄ q9_lo) ∗
      ((fsp + 1809#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1817#64) 7 ∗
      (((fsp + 1824#64) ↦₆₄ w32) ∗
       ((fsp + 1832#64) ↦₆₄ w40) ∗
       ((fsp + 1840#64) ↦₆₄ d48)) ∗
      ((fsp + 24#64) ↦₆₄ slot24_old) ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = c1 ∧
      sm.readReg64 .x8 = (EncoderFromPb.loByte w8).zeroExtend 64 ∧
      sm.readReg64 .x9 = w48 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x20 = fsp + 1792#64 ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x25 = fsp + 1792#64 ∧
      sm.readReg64 .x26 = l1 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = p1 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h8 := (pointsTo64_split_1_7 (pbA + 136#64) w8).symm
      have ha9 : pbA + 136#64 + 1#64 = pbA + 137#64 := by bv_omega
      rw [ha9] at h8
      have htri := v7_triple64_to_byte_qword_tail7 (pbA + 136#64) w8 w16 w24
      simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
        BitVec.add_assoc, BitVec.reduceAdd] at htri
      have hpb_mid :
          ((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
          ((pbA + 137#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
          ((pbA + 144#64) ↦₆₄ w16) ∗ ((pbA + 152#64) ↦₆₄ w24) =
          ((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
          ((pbA + 137#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
          ((pbA + 145#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
          ((pbA + 153#64) ↦ₛ EncoderFromPb.hiBytes7 w24) := by
        rw [← sepConj_assoc, h8, htri]
        ac_rfl
      refine Entails.trans (Entails.of_eq (show _ =
        (((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
         ((pbA + 137#64) ↦ₛ EncoderFromPb.hiBytes7 w8) ∗
         ((pbA + 144#64) ↦₆₄ w16) ∗ ((pbA + 152#64) ↦₆₄ w24)) ∗
        (((pbA + 128#64) ↦₆₄ cap_enc) ∗
         (((pbA + 160#64) ↦₆₄ w32) ∗
          ((pbA + 168#64) ↦₆₄ w40) ∗
          ((pbA + 176#64) ↦₆₄ w48)) ∗
         v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
         ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
         ((fsp + 1800#64) ↦₈ b8) ∗
         ((fsp + 1801#64) ↦₆₄ q9_lo) ∗
         ((fsp + 1809#64) ↦₆₄ q9_hi) ∗
         memRegion (fsp + 1817#64) 7 ∗
         (((fsp + 1824#64) ↦₆₄ w32) ∗
          ((fsp + 1832#64) ↦₆₄ w40) ∗
          ((fsp + 1840#64) ↦₆₄ d48)) ∗
         ((fsp + 24#64) ↦₆₄ slot24_old) ∗
         Frame) by ac_rfl)) ?_
      rw [hpb_mid]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2
      ⟨hsp2, hx0_2, hx1_2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2⟩
    refine EncoderFromPb.seq_clean (mid := entry + 3688#64)
      (P_mid :=
        ((pbA + 128#64) ↦₆₄ cap_enc) ∗
        (((pbA + 136#64) ↦₆₄ w8) ∗
         ((pbA + 144#64) ↦₆₄ w16) ∗
         ((pbA + 152#64) ↦₆₄ w24) ∗
         ((pbA + 160#64) ↦₆₄ w32) ∗
         ((pbA + 168#64) ↦₆₄ w40) ∗
         ((pbA + 176#64) ↦₆₄ w48)) ∗
        v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
        ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
        ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte w8) ∗
        ((fsp + 1801#64) ↦₆₄ q9_lo) ∗
        ((fsp + 1809#64) ↦₆₄ q9_hi) ∗
        memRegion (fsp + 1817#64) 7 ∗
        (((fsp + 1824#64) ↦₆₄ w32) ∗
         ((fsp + 1832#64) ↦₆₄ w40) ∗
         ((fsp + 1840#64) ↦₆₄ d48)) ∗
        ((fsp + 24#64) ↦₆₄ slot24_old) ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = c1 ∧
        sm.readReg64 .x9 = w48 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1792#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        sm.readVReg128 0#5 = (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
          EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have htri_pb := (v7_triple64_to_byte_qword_tail7 (pbA + 136#64) w8 w16 w24).symm
        simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
          BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at htri_pb
        refine Entails.trans (Entails.of_eq (show _ =
          (((pbA + 136#64) ↦₈ EncoderFromPb.loByte w8) ∗
           ((pbA + 137#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
           ((pbA + 145#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
           ((pbA + 153#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
          (((pbA + 128#64) ↦₆₄ cap_enc) ∗
           (((pbA + 160#64) ↦₆₄ w32) ∗
            ((pbA + 168#64) ↦₆₄ w40) ∗
            ((pbA + 176#64) ↦₆₄ w48)) ∗
           v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
           ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
           ((fsp + 1800#64) ↦₈ EncoderFromPb.loByte w8) ∗
           ((fsp + 1801#64) ↦₆₄ q9_lo) ∗
           ((fsp + 1809#64) ↦₆₄ q9_hi) ∗
           memRegion (fsp + 1817#64) 7 ∗
           (((fsp + 1824#64) ↦₆₄ w32) ∗
            ((fsp + 1832#64) ↦₆₄ w40) ∗
            ((fsp + 1840#64) ↦₆₄ d48)) ∗
           ((fsp + 24#64) ↦₆₄ slot24_old) ∗
           Frame) by ac_rfl)) ?_
        rw [htri_pb]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · intro s3 hpc3 hrun3
        ⟨hsp3, hx0_3, hx1_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hq0_3, htr3⟩
      refine EncoderFromPb.seq_clean (mid := entry + 3712#64)
        (P_mid :=
          (∃∗ u16 : BitVec 64,
            ((fsp + 1800#64) ↦₆₄ w8) ∗
            ((fsp + 1808#64) ↦₆₄ w16) ∗
            ((fsp + 1816#64) ↦₆₄ u16)) ∗
          memRegion (pbA + 128#64) 56 ∗
          v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
          ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
          (((fsp + 1824#64) ↦₆₄ w32) ∗
           ((fsp + 1832#64) ↦₆₄ w40) ∗
           ((fsp + 1840#64) ↦₆₄ w48)) ∗
          ((fsp + 24#64) ↦₆₄ c1) ∗
          Frame)
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = fsp + 1888#64 ∧
          sm.readReg64 .x1 = fsp + 1792#64 ∧
          sm.readReg64 .x8 = w24 ∧
          sm.readReg64 .x19 = out ∧
          sm.readReg64 .x20 = fsp + 1792#64 ∧
          sm.readReg64 .x21 = x21_val ∧
          sm.readReg64 .x22 = cap_dec ∧
          sm.readReg64 .x23 = x23_val ∧
          sm.readReg64 .x24 = c2 ∧
          sm.readReg64 .x25 = fsp + 1888#64 ∧
          sm.readReg64 .x26 = l1 ∧
          sm.readReg64 .x27 = pbA ∧
          sm.readReg64 .x28 = p1 ∧
          TraceCalleeSaved sm s0)
        ?_ ?_
      · wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hpb_56 :
              ((pbA + 128#64) ↦₆₄ cap_enc) ∗
              ((pbA + 136#64) ↦₆₄ w8) ∗
              ((pbA + 144#64) ↦₆₄ w16) ∗
              ((pbA + 152#64) ↦₆₄ w24) ∗
              ((pbA + 160#64) ↦₆₄ w32) ∗
              ((pbA + 168#64) ↦₆₄ w40) ∗
              ((pbA + 176#64) ↦₆₄ w48) ⊢
              memRegion (pbA + 128#64) 56 := by
            have h := v7_encWordsAt_entails_56 (pbA + 128#64) cap_enc w8 w16 w24 w32 w40 w48
            unfold v7_encTailWordsAt at h
            simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h
            exact h
          have hfsp_q := v7_byte_qword_mem7_to_triple64 (fsp + 1800#64) w8 w16 w24
          simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
            BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hfsp_q
          refine Entails.trans (Entails.of_eq (show _ =
            (((fsp + 1800#64) ↦₈ EncoderFromPb.loByte w8) ∗
             ((fsp + 1801#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
             ((fsp + 1809#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
             memRegion (fsp + 1817#64) 7) ∗
            ((((pbA + 128#64) ↦₆₄ cap_enc) ∗
              ((pbA + 136#64) ↦₆₄ w8) ∗
              ((pbA + 144#64) ↦₆₄ w16) ∗
              ((pbA + 152#64) ↦₆₄ w24) ∗
              ((pbA + 160#64) ↦₆₄ w32) ∗
              ((pbA + 168#64) ↦₆₄ w40) ∗
              ((pbA + 176#64) ↦₆₄ w48)) ∗
             (v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48 ∗
              ((fsp + 1792#64) ↦₆₄ cap_enc) ∗
              (((fsp + 1824#64) ↦₆₄ w32) ∗
               ((fsp + 1832#64) ↦₆₄ w40) ∗
               ((fsp + 1840#64) ↦₆₄ w48)) ∗
              ((fsp + 24#64) ↦₆₄ c1) ∗
              Frame)) by ac_rfl)) ?_
          exact sepConj_mono hfsp_q (sepConj_mono_left hpb_56)
        · wp_done
      · intro s4 hpc4 hrun4
          ⟨hsp4, hx0_4, hx1_4, hx8_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, htr4⟩
        wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
        apply ProofLib.SepWP.exists_left; intro u16
        wp_steps
        refine EncoderFromPb.align_pre ?_ ?_
        · have hpack := v7_encAt_pack A (fsp + 1792#64) cap_enc encPb w8 w16 w24 w32 w40 w48
          unfold v7_encTailWordsAt at hpack
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
          refine Entails.trans (Entails.of_eq (show _ =
            memRegion (pbA + 128#64) 56 ∗
            (((fsp + 1792#64) ↦₆₄ cap_enc) ∗
             (((fsp + 1800#64) ↦₆₄ w8) ∗
              ((fsp + 1808#64) ↦₆₄ w16) ∗
              ((fsp + 1816#64) ↦₆₄ w24) ∗
              ((fsp + 1824#64) ↦₆₄ w32) ∗
              ((fsp + 1832#64) ↦₆₄ w40) ∗
              ((fsp + 1840#64) ↦₆₄ w48)) ∗
             v7_encTailHeap A cap_enc encPb w8 w16 w24 w32 w40 w48) ∗
            ((fsp + 24#64) ↦₆₄ c1) ∗
            Frame by ac_rfl)) ?_
          exact sepConj_mono_right (sepConj_mono_left hpack)
        · wp_done

/-- Step the `bl 0x62188` instruction at `+3716` to `<PolyEncoder>::from_pb` entry (`+32996`). -/
theorem v7_bl_encoder_3716_to_32996
    {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3716#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1792#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 32996#64) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1792#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = fsp + 1792#64 ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x28 = p1 ∧
        sm.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3720#64 ∧
        TraceCalleeSaved sm s0) := by
  states_from_pb_fetches_range b (Rust.withPanics ext) 3716 4
  dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::from_pb" = entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 3. `<PolyEncoder>::from_pb = Err` Cleanup (`+3720 -> +3732 -> +4632`) -/

theorem v7_resultPolyEncoder_err_entails_tag_392 (A : RustAlloc) (fsp : BitVec 64)
    (err : PolynomialError) :
    resultPolyEncoderFromPbAt A (fsp + 1888#64) (.error err) ⊢
      ((fsp + 1888#64) ↦₆₄ 2#64) ∗ memRegion (fsp + 1896#64) 392 := by
  dsimp only [resultPolyEncoderFromPbAt, polyEncoderNicheTag,
    resultPolyEncoderErrByteOff, resultPolyEncoderErrTailSize]
  have hm8 : ((fsp + 1896#64) ↦₈ polynomialErrorByte err) ∗ memRegion (fsp + 1897#64) 391 ⊢
      memRegion (fsp + 1896#64) 392 := by
    rw [ProofLib.memRegion_split' (b := fsp + 1896#64) (n := 1) (k := 391)
          (b' := fsp + 1897#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (fsp + 1896#64) (polynomialErrorByte err))
  have ha1896 : (fsp + 1888#64) + 8#64 = fsp + 1896#64 := by bv_omega
  have ha1897 : (fsp + 1888#64) + 9#64 = fsp + 1897#64 := by bv_omega
  rw [ha1896, ha1897]
  exact sepConj_mono_right hm8

theorem v7_1888_tag_392_to_memRegion_400 (fsp tag : BitVec 64) :
    ((fsp + 1888#64) ↦₆₄ tag) ∗ memRegion (fsp + 1896#64) 392 ⊢
      memRegion (fsp + 1888#64) 400 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 8) (k := 392)
        (b' := fsp + 1896#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+3720 -> +3732`,
deallocates all 5 vectors of `uc` and `optDec` via `v7_cleanup_3732`, and reaches `+4632`. -/
theorem v7_enc_err_3720_to_4632
    {A : RustAlloc} {F : ShaCompress} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (err : PolynomialError) (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hfsp_align : ((s0.sp - 2400#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 2400#64 hsp0_align (by decide)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_resultPolyEncoder_err_entails_tag_392 A (s0.sp - 2400#64) err)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (v7_ct1SentHeap_entails_dealloc A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5)))))) ?_
  refine EncoderFromPb.seq_clean
    (mid := (tripleRatchetProgAtExt b ext).fnAddr statesFromPbName + 3732#64)
    (P_mid :=
      memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
       (vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗
        vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5) ∗
       (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
       A.pool ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x28 = p1 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · states_from_pb_fetches_range b (Rust.withPanics ext) 3720 12
    dsimp only [tripleRatchetProgAtExt, statesFromPbName, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "<spqr::v1::chunked::states::States>::from_pb" = entry
    examples_hide_fetches
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have h400 := v7_1888_tag_392_to_memRegion_400 (s0.sp - 2400#64) 2#64
      refine Entails.trans (Entails.of_eq (show _ =
        (((s0.sp - 2400#64 + 1888#64) ↦₆₄ 2#64) ∗ memRegion (s0.sp - 2400#64 + 1896#64) 392) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
         v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
         (vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗
          vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5) ∗
         (((pbA + 184#64) ↦₆₄ cap_dec) ∗
          v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec optDec) ∗
         A.pool ∗ Frame) by ac_rfl)) ?_
      exact sepConj_mono_left h400
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
    rw [v7_ct1SentWordsAt_1264_eq_spill_other]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (v7_cleanup_3732 hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec
          (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
           memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame)
          hcap_dec hsp0_align hpc2 hrun2 hsp2 hx19_2 hx22_2 hx24_2 hx27_2 hx28_2 htr2) ?_)
    intro s3 P3 hrun3 hpc3 ⟨hP3, hq⟩
    refine ⟨Entails.trans hP3 ?_, hq⟩
    have h1264 :
        v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
        v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ⊢
        memRegion ((s0.sp - 2400#64) + 1264#64) 128 := by
      rw [← v7_ct1SentWordsAt_1264_eq_spill_other]
      exact v7_ct1SentWordsAt_entails_128 ((s0.sp - 2400#64) + 1264#64)
        c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch
    refine Entails.trans (Entails.of_eq (show _ =
      (v7_ct1SentSpillCells (s0.sp - 2400#64) p2 c3 p3 c4 p4 c5 p5 ∗
       v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch) ∗
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
       memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       memRegion (pbA + 184#64) 40 ∗
       A.pool ∗
       Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by ac_rfl))

/-! ## 4. `<PolyEncoder>::from_pb` `Ok` Move (`+3720 -> +7260 -> +7348`) & `receivingEk = none` (`+7348 -> +10556 -> +4632`) -/

def v7_polyEncoderTag (enc : PolyEncoder) : BitVec 64 :=
  match enc.s with
  | .points _ => 0#64
  | .polys _ => 1#64

theorem v7_polyEncoderTag_eq (enc : PolyEncoder) :
    v7_polyEncoderTag enc = 0#64 ∨ v7_polyEncoderTag enc = 1#64 := by
  unfold v7_polyEncoderTag
  cases enc.s <;> simp

theorem v7_pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsTo32_eq_pointsToBytes]
  change (a ↦ₛ unpack32 lo) ∗ ((a + BitVec.ofNat 64 (unpack32 lo).length) ↦ₛ unpack32 hi) = _
  rw [← ProofLib.pointsToBytes_append a (unpack32 lo) (unpack32 hi)]
  congr 1
  unfold unpack64 unpack32
  simp only [List.singleton_append, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem v7_polyEncoderAt_relocate (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ bs : { l : List (BitVec 8) // l.length = 384 },
      ∃∗ hi32 : BitVec 32, ∃∗ P_heap : SepProp,
        ⌜((a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
           ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
        ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗
        P_heap := by
  unfold polyEncoderAt encoderStateAt polyEncoderPointsTag polyEncoderPolysTag
    polyEncoderVecsOff polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize v7_polyEncoderTag
  rw [ProofLib.memRegion_four (a1 + 396#64)]
  cases hs : enc.s with
  | points pts =>
    dsimp only
    rw [pointListOf_eq_vecGF16ListOf A pts (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (pts.map Point.value) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hpts_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (pts.map Point.value)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (pts.map Point.value) hpins_len, List.length_map, hpts_len.1]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v7_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (pts.map Point.value), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (pts.map Point.value)) ?_))
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    rw [pointListOf_eq_vecGF16ListOf A pts (a2 + 8#64),
        ← v7_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (pts.map Point.value) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 0#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (pts.map Point.value)) ∗
       vecGF16HeapList A pins (pts.map Point.value)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hpts_len (Entails.of_eq (by ac_rfl))
  | polys ps =>
    dsimp only
    rw [polyListOf_eq_vecGF16ListOf A ps (a1 + 8#64)]
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (vecGF16ListOf_entails_headers_heaps A (ps.map LibsignalSpqrV1.Poly.coefficients) (a1 + 8#64))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply Entails.sepExists_elim; intro hi32
    apply Entails.sepExists_elim; intro pins
    apply Entails.pure_left; intro hps_len
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpins_len
    have hbs_len : (vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)).length = 384 := by
      rw [length_vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients) hpins_len, List.length_map, hps_len]
      rfl
    have ha1_396 : a1 + 396#64 = (a1 + 392#64) + 4#64 := by bv_omega
    rw [ha1_396, v7_pointsTo32_pair_eq_pointsTo64 (a1 + 392#64) enc.idx hi32]
    refine Entails.sepExists_right ⟨vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients), hbs_len⟩
      (Entails.sepExists_right hi32
        (Entails.sepExists_right (vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ?_))
    refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
    rw [polyListOf_eq_vecGF16ListOf A ps (a2 + 8#64),
        ← v7_pointsTo32_pair_eq_pointsTo64 (a2 + 392#64) enc.idx hi32]
    have ha2_396 : (a2 + 392#64) + 4#64 = a2 + 396#64 := by bv_omega
    rw [ha2_396]
    have hvec2 := headers_heaps_entails_vecGF16ListOf A pins (ps.map LibsignalSpqrV1.Poly.coefficients) (a2 + 8#64) hpins_len
    have hm4 : ((a2 + 396#64) ↦₃₂ hi32) ⊢ memRegion (a2 + 396#64) 4 := by
      rw [ProofLib.memRegion_four (a2 + 396#64)]
      exact Entails.sepExists_right hi32 (Entails.refl _)
    refine Entails.trans (Entails.of_eq (show _ =
      (a2 ↦₆₄ 1#64) ∗
      (((a2 + 8#64) ↦ₛ vecHeadersBytesOf pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
       vecGF16HeapList A pins (ps.map LibsignalSpqrV1.Poly.coefficients)) ∗
      ((a2 + 392#64) ↦₃₂ enc.idx) ∗
      ((a2 + 396#64) ↦₃₂ hi32) by ac_rfl)) ?_
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono hvec2 (sepConj_mono_right hm4))) ?_
    exact Entails.pure_right hps_len (Entails.of_eq (by ac_rfl))

theorem v7_bs384_w392_split_368 (bs : List (BitVec 8)) (hbs : bs.length = 384) (w392 : BitVec 64) :
    ∃ (w8 w16 w24 : BitVec 64) (tail368 : { l : List (BitVec 8) // l.length = 368 }),
      ∀ a : BitVec 64,
        ((a + 8#64) ↦ₛ bs) ∗ ((a + 392#64) ↦₆₄ w392) =
          ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦₆₄ w16) ∗
          ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ tail368.val) := by
  have ht0 : (bs.take 8).length = 8 := by rw [List.length_take, hbs]; decide
  have ht1 : ((bs.drop 8).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  have ht2 : ((bs.drop 16).take 8).length = 8 := by rw [List.length_take, List.length_drop, hbs]; decide
  obtain ⟨w8, hw8⟩ := ProofLib.exists_unpack64_of_length_8 ht0
  obtain ⟨w16, hw16⟩ := ProofLib.exists_unpack64_of_length_8 ht1
  obtain ⟨w24, hw24⟩ := ProofLib.exists_unpack64_of_length_8 ht2
  have htail_len : (bs.drop 24 ++ unpack64 w392).length = 368 := by
    rw [List.length_append, List.length_drop, hbs, unpack64_length]
  refine ⟨w8, w16, w24, ⟨bs.drop 24 ++ unpack64 w392, htail_len⟩, fun a => ?_⟩
  have hbs0 : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have hbs1 : bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop 16 := by
    change bs.drop 8 = (bs.drop 8).take 8 ++ bs.drop (8 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hbs2 : bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop 24 := by
    change bs.drop 16 = (bs.drop 16).take 8 ++ bs.drop (16 + 8)
    rw [← List.drop_drop, List.take_append_drop]
  have hp0 : ((a + 8#64) ↦ₛ bs) =
      ((a + 8#64) ↦₆₄ w8) ∗ ((a + 16#64) ↦ₛ bs.drop 8) := by
    conv_lhs => rw [hbs0]
    rw [ProofLib.pointsToBytes_append (a + 8#64) (bs.take 8) (bs.drop 8), ht0,
        hw8, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha16 : (a + 8#64) + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
    rw [ha16]
  have hp1 : ((a + 16#64) ↦ₛ bs.drop 8) =
      ((a + 16#64) ↦₆₄ w16) ∗ ((a + 24#64) ↦ₛ bs.drop 16) := by
    conv_lhs => rw [hbs1]
    rw [ProofLib.pointsToBytes_append (a + 16#64) ((bs.drop 8).take 8) (bs.drop 16), ht1,
        hw16, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha24 : (a + 16#64) + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
    rw [ha24]
  have hp2 : ((a + 24#64) ↦ₛ bs.drop 16) =
      ((a + 24#64) ↦₆₄ w24) ∗ ((a + 32#64) ↦ₛ bs.drop 24) := by
    conv_lhs => rw [hbs2]
    rw [ProofLib.pointsToBytes_append (a + 24#64) ((bs.drop 16).take 8) (bs.drop 24), ht2,
        hw24, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha32 : (a + 24#64) + BitVec.ofNat 64 8 = a + 32#64 := by bv_omega
    rw [ha32]
  have hp3 : ((a + 32#64) ↦ₛ bs.drop 24) ∗ ((a + 392#64) ↦₆₄ w392) =
      ((a + 32#64) ↦ₛ (bs.drop 24 ++ unpack64 w392)) := by
    rw [ProofLib.pointsToBytes_append (a + 32#64) (bs.drop 24) (unpack64 w392),
        List.length_drop, hbs, ← ProofLib.pointsTo64_eq_pointsToBytes]
    have ha392 : (a + 32#64) + BitVec.ofNat 64 (384 - 24) = a + 392#64 := by bv_omega
    rw [ha392]
  rw [hp0, hp1, hp2]
  simp only [sepConj_assoc, hp3]

theorem v7_polyEncoderAt_relocate_368 (A : RustAlloc) (a1 a2 : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a1 enc ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64,
      ∃∗ tail368 : { l : List (BitVec 8) // l.length = 368 },
      ∃∗ P_heap : SepProp,
        ⌜((a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗ ((a2 + 24#64) ↦₆₄ w24) ∗
          ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap ⊢
            polyEncoderAt A a2 enc)⌝ ∗
        (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
        ((a1 + 8#64) ↦₆₄ w8) ∗
        ((a1 + 16#64) ↦₆₄ w16) ∗
        ((a1 + 24#64) ↦₆₄ w24) ∗
        ((a1 + 32#64) ↦ₛ tail368.val) ∗
        P_heap := by
  refine Entails.trans (v7_polyEncoderAt_relocate A a1 a2 enc) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro hi32
  apply Entails.sepExists_elim; intro P_heap
  apply Entails.pure_left; intro hreloc
  obtain ⟨w8, w16, w24, tail368, hsplit⟩ := v7_bs384_w392_split_368 bs.val bs.property (hi32 ++ enc.idx)
  have h1 := hsplit a1
  have h2 := hsplit a2
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right tail368
      (Entails.sepExists_right P_heap ?_))))
  refine Entails.pure_right ?_ ?_
  · refine Entails.trans ?_ hreloc
    refine Entails.of_eq ?_
    calc
      (a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
        ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val) ∗ P_heap
        = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a2 + 8#64) ↦₆₄ w8) ∗ ((a2 + 16#64) ↦₆₄ w16) ∗
           ((a2 + 24#64) ↦₆₄ w24) ∗ ((a2 + 32#64) ↦ₛ tail368.val)) ∗ P_heap := by ac_rfl
      _ = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a2 + 8#64) ↦ₛ bs.val) ∗ ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx))) ∗ P_heap := by rw [← h2]
      _ = (a2 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a2 + 8#64) ↦ₛ bs.val) ∗
          ((a2 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap := by ac_rfl
  · refine Entails.of_eq ?_
    calc
      (a1 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a1 + 8#64) ↦ₛ bs.val) ∗
        ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx)) ∗ P_heap
        = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a1 + 8#64) ↦ₛ bs.val) ∗ ((a1 + 392#64) ↦₆₄ (hi32 ++ enc.idx))) ∗ P_heap := by ac_rfl
      _ = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗
          (((a1 + 8#64) ↦₆₄ w8) ∗ ((a1 + 16#64) ↦₆₄ w16) ∗
           ((a1 + 24#64) ↦₆₄ w24) ∗ ((a1 + 32#64) ↦ₛ tail368.val)) ∗ P_heap := by rw [h1]
      _ = (a1 ↦₆₄ v7_polyEncoderTag enc) ∗ ((a1 + 8#64) ↦₆₄ w8) ∗
          ((a1 + 16#64) ↦₆₄ w16) ∗ ((a1 + 24#64) ↦₆₄ w24) ∗
          ((a1 + 32#64) ↦ₛ tail368.val) ∗ P_heap := by ac_rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v7_polyEncoderTag_sub_two_beq_zero (enc : PolyEncoder) :
    (v7_polyEncoderTag enc - 2#64 == 0#64) = false := by
  rcases v7_polyEncoderTag_eq enc with h | h <;> rw [h] <;> rfl

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x20_add_105_sext (fsp : BitVec 64) :
    (fsp + 1792#64) + (105#64).signExtend 64 = fsp + 1897#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x20_add_105 (fsp : BitVec 64) :
    fsp + 1792#64 + 105#64 = fsp + 1897#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1897_add_8 (fsp : BitVec 64) :
    fsp + 1897#64 + 8#64 = fsp + 1905#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x25_add_32 (fsp : BitVec 64) :
    fsp + 1888#64 + 32#64 = fsp + 1920#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_896_add_8 (fsp : BitVec 64) :
    fsp + 896#64 + 8#64 = fsp + 904#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x23_add_63_sext (fsp : BitVec 64) :
    (fsp + 848#64) + (63#64).signExtend 64 = fsp + 911#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_x23_add_63 (fsp : BitVec 64) :
    fsp + 848#64 + 63#64 = fsp + 911#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1392_add_32 (fsp : BitVec 64) :
    fsp + 1392#64 + 32#64 = fsp + 1424#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1264_add_137_sext (fsp : BitVec 64) :
    (fsp + 1264#64) + (137#64).signExtend 64 = fsp + 1401#64 := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1264_add_137 (fsp : BitVec 64) :
    fsp + 1264#64 + 137#64 = fsp + 1401#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_fsp_1401_add_8 (fsp : BitVec 64) :
    fsp + 1401#64 + 8#64 = fsp + 1409#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
theorem v7_zext32_setWidth8 (b : BitVec 8) :
    (b.zeroExtend 32).setWidth 8 = b := by bv_kernel

theorem v7_hiBytes7_eq_loBytes7_lsr8 (w : BitVec 64) :
    EncoderFromPb.hiBytes7 w = EncoderFromPb.loBytes7 (w >>> 8) := by
  change [_, _, _, _, _, _, _] = [_, _, _, _, _, _, _]
  refine congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·)
    (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (_ :: ·) (congrArg (· :: []) ?_))))))
  all_goals bv_kernel

theorem v7_lsr8_lsl8 (v : BitVec 64) :
    (v >>> 8) <<< 8 = v &&& 0xffffffffffffff00#64 := by
  bv_kernel

theorem v7_unshift_lsr56 (w0 v : BitVec 64) :
    (unshiftWord w0 (loByte v)) >>> 56 = v &&& 0xff#64 := by
  unfold unshiftWord loByte
  bv_kernel

theorem v7_overlapWord7_unshift_lsr8 (w0 w8 : BitVec 64) :
    overlapWord7 (unshiftWord w0 (loByte w8)) (w8 >>> 8) = w8 := by
  unfold overlapWord7
  rw [v7_unshift_lsr56 w0 w8, v7_lsr8_lsl8 w8]
  bv_kernel

theorem v7_pointsTo64_split_7_1 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [(w >>> 56).setWidth 8]) := by
  rw [pointsTo64_eq_pointsToBytes]
  change (a ↦ₛ unpack64 w) =
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗
    ((a + BitVec.ofNat 64 (EncoderFromPb.loBytes7 w).length) ↦ₛ [(w >>> 56).setWidth 8])
  rw [← ProofLib.pointsToBytes_append a (EncoderFromPb.loBytes7 w) [(w >>> 56).setWidth 8]]
  rfl

theorem v7_pointsTo64_split_7_1_entails_8 (a w : BitVec 64) (b7 : BitVec 8) :
    (a ↦ₛ EncoderFromPb.loBytes7 w) ∗ ((a + 7#64) ↦ₛ [b7]) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_split a 7 1 (by decide)]
  refine sepConj_mono ?_ ?_
  · have hlen : (EncoderFromPb.loBytes7 w).length = 7 := rfl
    exact hlen ▸ ProofLib.pointsToBytes_entails_memRegion a (EncoderFromPb.loBytes7 w)
  · have hlen1 : ([b7] : List (BitVec 8)).length = 1 := rfl
    exact hlen1 ▸ ProofLib.pointsToBytes_entails_memRegion (a + 7#64) [b7]

theorem v7_fsp_1896_triple_rest (fsp w8 w16 w24 : BitVec 64) (R : SepProp) :
    ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ R =
      ((fsp + 1896#64) ↦₈ loByte w8) ∗
      ((fsp + 1897#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
      ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ R := by
  have h := v7_triple64_to_byte_qword_tail7 (fsp + 1896#64) w8 w16 w24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 1896#64) + 1#64)
        (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24) ∗ R =
        (((fsp + 1896#64) ↦₆₄ w8) ∗ ((fsp + 1904#64) ↦₆₄ w16) ∗ ((fsp + 1912#64) ↦₆₄ w24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v7_fsp_1905_realign_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 1913#64) ↦ₛ EncoderFromPb.hiBytes7 w24) ∗ Rest =
      ((fsp + 1905#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 1912#64) ↦₆₄ w24) ∗ Rest := by
  have ha1912 : (fsp + 1905#64) + 7#64 = fsp + 1912#64 := by bv_omega
  have ha1913 : (fsp + 1905#64) + 8#64 = fsp + 1913#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1905#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)
  rw [ha1913, ha1912, ← v7_hiBytes7_eq_loBytes7_lsr8 w24,
      v7_overlapWord7_unshift_lsr8 w16 w24] at h
  rw [← sepConj_assoc ((fsp + 1905#64) ↦₆₄ unshiftWord w16 (loByte w24)), h]
  simp only [sepConj_assoc]

theorem v7_fsp_904_realign_rest (fsp u1 d16 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ u1) ∗ ((fsp + 912#64) ↦₆₄ d16) ∗ Rest =
      ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 911#64) ↦₆₄ overlapWord7 u1 d16) ∗
      ((fsp + 919#64) ↦ₛ [(d16 >>> 56).setWidth 8]) ∗ Rest := by
  have hsplit := v7_pointsTo64_split_7_1 (fsp + 912#64) d16
  have ha919 : (fsp + 912#64) + 7#64 = fsp + 919#64 := by bv_omega
  rw [ha919] at hsplit
  have hover := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 904#64) u1 d16
  have ha912 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have ha911 : (fsp + 904#64) + 7#64 = fsp + 911#64 := by bv_omega
  rw [ha912, ha911] at hover
  rw [hsplit]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc ((fsp + 904#64) ↦₆₄ u1), hover]
  simp only [sepConj_assoc]

theorem v7_fsp_904_unrealign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 911#64) ↦₆₄ w24) ∗ Rest =
      ((fsp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 912#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest := by
  have hover := (pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 904#64)
    (unshiftWord w16 (loByte w24)) (w24 >>> 8)).symm
  have ha912 : (fsp + 904#64) + 8#64 = fsp + 912#64 := by bv_omega
  have ha911 : (fsp + 904#64) + 7#64 = fsp + 911#64 := by bv_omega
  rw [ha912, ha911, v7_overlapWord7_unshift_lsr8 w16 w24] at hover
  rw [← sepConj_assoc ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))), hover]
  simp only [sepConj_assoc]

theorem v7_fsp_904_realign_w24_rest (fsp w16 w24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
      ((fsp + 912#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗ Rest =
      ((fsp + 904#64) ↦ₛ EncoderFromPb.loBytes7 (unshiftWord w16 (loByte w24))) ∗
      ((fsp + 911#64) ↦₆₄ w24) ∗ Rest :=
  (v7_fsp_904_unrealign_w24_rest fsp w16 w24 Rest).symm

theorem v7_fsp_1400_triple_rest (fsp e8 e16 e24 : BitVec 64) (R : SepProp) :
    ((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24) ∗ R =
      ((fsp + 1400#64) ↦₈ loByte e8) ∗
      ((fsp + 1401#64) ↦₆₄ unshiftWord e8 (loByte e16)) ∗
      ((fsp + 1409#64) ↦₆₄ unshiftWord e16 (loByte e24)) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ R := by
  have h := v7_triple64_to_byte_qword_tail7 (fsp + 1400#64) e8 e16 e24
  rw [← EncoderFromPb.pointsTo64_pair_eq_pointsTo128 ((fsp + 1400#64) + 1#64)
        (unshiftWord e8 (loByte e16)) (unshiftWord e16 (loByte e24))] at h
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [show ((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24) ∗ R =
        (((fsp + 1400#64) ↦₆₄ e8) ∗ ((fsp + 1408#64) ↦₆₄ e16) ∗ ((fsp + 1416#64) ↦₆₄ e24)) ∗ R by ac_rfl,
      h]
  simp only [sepConj_assoc]

theorem v7_fsp_1409_realign_rest (fsp u1 e24 : BitVec 64) (Rest : SepProp) :
    ((fsp + 1409#64) ↦₆₄ u1) ∗
      ((fsp + 1417#64) ↦ₛ EncoderFromPb.hiBytes7 e24) ∗ Rest =
      ((fsp + 1409#64) ↦ₛ EncoderFromPb.loBytes7 u1) ∗
      ((fsp + 1416#64) ↦₆₄ overlapWord7 u1 (e24 >>> 8)) ∗ Rest := by
  have ha1416 : (fsp + 1409#64) + 7#64 = fsp + 1416#64 := by bv_omega
  have ha1417 : (fsp + 1409#64) + 8#64 = fsp + 1417#64 := by bv_omega
  have h := pointsTo64_loBytes7_eq_loBytes7_overlapWord7 (fsp + 1409#64) u1 (e24 >>> 8)
  rw [ha1417, ha1416, ← v7_hiBytes7_eq_loBytes7_lsr8 e24] at h
  rw [← sepConj_assoc ((fsp + 1409#64) ↦₆₄ u1), h]
  simp only [sepConj_assoc]

end CryptoVerification.SpqrV1.States.FromPb

