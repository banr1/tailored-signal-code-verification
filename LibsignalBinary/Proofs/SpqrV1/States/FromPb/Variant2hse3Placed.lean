/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 2 (`HeaderSent`, `+508`) — Part E3

Relocatable Block-`333` `receivingCt1` (`<PolyDecoder>::from_pb`) stage (`+9328..+9404`) and
error exits to `+9228`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed

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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hsdPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm, local wp_norm]
  v2hse3_bv_add_add_lit
  v2hse3_x23_add_193_sext
  v2hse3_x25_add_65_sext

/-! ## `receivingCt1 = none` Branch (`+9328 -> +11024 -> +9228`) -/

/-- At `+9328` (`b.eq +11024`), when `s1.pstate = addsPState64 noneCap 1#64`
(`receivingCt1 = none`), takes `b.eq +11024`, drops `[Poly; 16]` at `fsp + 1400`,
deallocates `(ca1, pa1)`, `(ca2, pa2)`, `(ca3, pa3)`, sets `x23 = 0#64`, and reaches `+9228`. -/
theorem v2hse3_none_dec_9328_to_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out ca1 pa1 ca2 pa2 ca3 pa3 : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx23_1 : s1.readReg64 .x23 = fsp + 1392#64)
    (hx26_1 : s1.readReg64 .x26 = ca3)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
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
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 11024#64)
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
  · dsimp only [noneCap] at hpstate1 ⊢
    change s1.pc = (blkPl_333).base + 9328#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11024#64) s1 _ _
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx23_2, hx26_2, htr2⟩
    exact v2hsd_cleanup_11024_to_9228_placed hA s0 s2 fsp out ca1 pa1 ca2 pa2 ca3 pa3 enc Frame
      hcl2 hfsp_align hpc2 hrun2 hsp2 hx19_2 hx23_2 hx26_2 htr2

/-! ## Copy `ProtoPolynomialDecoder` (`+9328 -> +9384`) and Call `<PolyDecoder>::from_pb` (`+9384 -> lsmpl.base 376`) -/

set_option maxHeartbeats 800000 in
/-- At `+9328` when `s1.pstate = addsPState64 d0 1#64` with `hd0 : d0.toNat < 2 ^ 63`,
falls through `b.eq +11024` and copies `(d0, d8, d16, d24, d32)` from `x22` and `fsp + 1040..1064`
into `fsp + 1848..1888`, reaching `+9384` with `x0 = fsp + 1888#64`, `x1 = fsp + 1848#64`,
`x19 = out`, `x20 = x20_val`, `x21 = x21_val`, `x22 = fsp + 1888#64`, `x23 = fsp + 848#64`,
`x25 = fsp + 1792#64`, `x26 = ca3`, `x28 = x28_val`. -/
theorem v2hse3_copy_dec_9328_to_9384_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val d0 d8 d16 d24 d32 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hd0 : d0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9328#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9384#64) s1
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
  change s1.pc = (blkPl_333).base + 9328#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9384#64) s1 _ _
  refine EncoderFromPb.seq_clean (mid := (blkPl_333).base + 9348#64)
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
    refine EncoderFromPb.seq_clean (mid := (blkPl_333).base + 9376#64)
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

/-- Execute `bl <PolyDecoder>::from_pb` at `+9384` to `<PolyDecoder>::from_pb` entry (`lsmpl.base 376`),
setting `x30 = lsmpl.base 333 + 9388#64`. -/
theorem v2hse3_bl_decoder_9384_to_35448_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 9384#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 P
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
        sm.readReg64 .x30 = lsmpl.base 333 + 9388#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 9384#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    (lsmpl.base 376) s1 P _
  wp_steps
  dsimp only [blkPl_333, Obj.MultiPlacedLib.blockPlacement]
  wp_done

/-! ## `<PolyDecoder>::from_pb` Return Branches (`+9388 -> +9228` on `Err`, `+9388 -> +9404` on `Ok`) -/

/-- At `+9388`, when `resultPolyDecoderFromPbAt A (fsp + 1888#64) (.error err)` holds,
loads `noneCap` from `[sp, #0x760]`, stores `noneCap` to `[sp, #0xd8]` (`fsp + 216#64`),
takes `b.eq +11240`, drops `enc` at `fsp + 1392` and `uc` at `fsp + 1264` via
`v2hsd_cleanup_11240_to_9228_placed`, and reaches `+9228` with `x23 = 0#64`. -/
theorem v2hse3_err_dec_9388_to_9228_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out w216_old : BitVec 64)
    (enc : PolyEncoder) (uc : LibsignalSpqrV1.Unchunked.SendEk.EkSent (spqrAuthApi F))
    (err : PolynomialError) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9228#64) s1
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
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 11240#64)
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
  · dsimp only [noneCap] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 9388#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11240#64) s1 _ _
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
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    have h11240 := v2hsd_cleanup_11240_to_9228_placed hA s0 s2 fsp out enc uc
      (memRegion (fsp + 1888#64) 400 ∗ ((fsp + 216#64) ↦₆₄ noneCap) ∗ Frame)
      hcl2 hfsp_align hpc2 hrun2 hsp2 hx19_2 htr2
    exact SepWP.mono h11240 fun sm Pm _ _ ⟨hPm, hq⟩ =>
      ⟨Entails.trans hPm (Entails.of_eq (by ac_rfl)), hq⟩

/-- At `+9388`, when `((fsp + 1888#64) ↦₆₄ dw0)` holds with `hdw0 : dw0.toNat < 2 ^ 63`,
loads `dw0` from `[sp, #0x760]`, stores `dw0` to `[sp, #0xd8]` (`fsp + 216#64`),
falls through `b.eq +11240`, and reaches `+9404` preserving `x19`, `x20`, `x21`, `x22`,
`x23`, `x25`, `x26`, `x28`. -/
theorem v2hse3_ok_dec_9388_to_9404_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out x20_val x21_val ca3 x28_val dw0 w216_old : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hdw0 : dw0.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 9388#64)
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
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 9404#64) s1
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
  change s1.pc = (blkPl_333).base + 9388#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 9404#64) s1 _ _
  wp_steps
  refine EncoderFromPb.align_pre (Entails.of_eq (by ac_rfl)) ?_
  wp_done

end LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed

namespace CryptoVerification.SpqrV1.States.FromPb

export LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2hse3Placed (
  v2hse3_none_dec_9328_to_9228_placed
  v2hse3_copy_dec_9328_to_9384_placed
  v2hse3_bl_decoder_9384_to_35448_placed
  v2hse3_err_dec_9388_to_9228_placed
  v2hse3_ok_dec_9388_to_9404_placed
)

end CryptoVerification.SpqrV1.States.FromPb
