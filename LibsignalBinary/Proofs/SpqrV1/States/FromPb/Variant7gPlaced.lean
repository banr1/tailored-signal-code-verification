/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7f
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7fPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part G

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7g.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.SpqrV1.States.FromPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 blkPl_374 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

variable [LibsignalPlacement]

/-! ## 1. `s.sendingCt1 = none` Path (`+3552 -> +7100 -> +4632`) -/

/-- When `<Ct1Sent>::from_pb` returns `Ok(uc)` at `fsp + 1888..2016` and `[pbA + 128] = noneCap`
(`s.sendingCt1 = none`), spills `uc` to `fsp + 1264..1392`, branches to `+7100`, deallocates
all 5 vectors of `uc` and `optDec`, and reaches `+4632`. -/
theorem v7_uc_ok_none_enc_3552_to_4632_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
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
    (mid := lsmpl.base 333 + 7100#64)
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
    (v7_uc_ok_spill_3552_to_7100_placed s0 s1 (s0.sp - 2400#64) out pbA cap_dec
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch _
      hfsp_align hc1 hpc1 hrun1 hsp1 hx19_1 hx22_1 hx27_1 htr1) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx1_2, hx19_2, hx22_2, hx24_2, hx27_2, hx28_2, htr2⟩
  rw [v7_ct1SentWordsAt_1264_eq_spill_other]
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.mono
      (v7_cleanup_7100_placed hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec
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

/-! ## 2. `<PolyEncoder>::from_pb` Copy (`+3652 -> +3716`) and Call (`+3716 -> lsmpl.base 374`) -/

set_option maxHeartbeats 800000 in
/-- Copy `ProtoPolynomialEncoder` (`56`B) from `pbA + 128` to `fsp + 1792` (`sp + 0x700`),
store `c1` (`x1`) to `[sp, #0x18]`, and set `x0 = fsp + 1888`, `x1 = fsp + 1792`,
`x20 = fsp + 1792`, `x25 = fsp + 1888` at `+3652 -> +3716`. -/
theorem v7_copy_enc_3652_to_3716_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_enc cap_dec c1 c2 l1 p1 x21_val x23_val slot24_old : BitVec 64)
    (encPb : ProtoPolynomialEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3652#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 3716#64) s1
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
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 3680#64)
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
  · change s1.pc = (blkPl_333).base + 3652#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3680#64) s1 _ _
    wp_steps
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
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 3688#64)
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
    · change s2.pc = (blkPl_333).base + 3680#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 3688#64) s2 _ _
      wp_steps
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
      refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 3712#64)
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
      · change s3.pc = (blkPl_333).base + 3688#64 at hpc3
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3712#64) s3 _ _
        wp_steps
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
        change s4.pc = (blkPl_333).base + 3712#64 at hpc4
        change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
          ((blkPl_333).base + 3716#64) s4 _ _
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

/-- Step the `bl` instruction at `+3716` to `<PolyEncoder>::from_pb` entry (`lsmpl.base 374`). -/
theorem v7_bl_encoder_3716_to_32996_placed
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 3716#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 374) s1 P
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
        sm.readReg64 .x30 = lsmpl.base 333 + 3720#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 3716#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_374).base) s1 P
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
      sm.readReg64 .x30 = (blkPl_333).base + 3720#64 ∧
      TraceCalleeSaved sm s0)
  wp_steps
  wp_done

/-! ## 3. `<PolyEncoder>::from_pb = Err` Cleanup (`+3720 -> +3732 -> +4632`) -/

/-- When `<PolyEncoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+3720 -> +3732`,
deallocates all 5 vectors of `uc` and `optDec` via `v7_cleanup_3732_placed`, and reaches `+4632`. -/
theorem v7_enc_err_3720_to_4632_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA cap_dec c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (err : PolynomialError) (optDec : Option ProtoPolynomialDecoder)
    (Frame : SepProp)
    (hcap_dec : v7_optDecoderCapProp cap_dec optDec)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
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
    (mid := lsmpl.base 333 + 3732#64)
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
  · wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    change s1.pc = (blkPl_333).base + 3720#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 3732#64) s1 _ _
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
        (v7_cleanup_3732_placed hA s0 s2 out pbA cap_dec c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 optDec
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

end CryptoVerification.SpqrV1.States.FromPb
