/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant1bPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7g
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7bPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7cPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant7h
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::from_pb`: Placed Variant 7 (`Ct1Sampled`, Block `333`) — Part H

Relocatable (`Obj.MultiPlacedLib`) migration of `Variant7h.lean`.
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
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.Variant2aPlaced

open CryptoVerification (blkPC_333 lsmpl lsProg_333 blkPl_333 blkPl_376 lsρ)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_333
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  extractLsb'_0_64_append extractLsb'_64_64_append
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm, local wp_norm]
  v7_polyEncoderTag_sub_two_beq_zero
  v7_x20_add_105_sext
  v7_x20_add_105
  v7_fsp_1897_add_8
  v7_x25_add_32
  v7_fsp_896_add_8
  v7_x23_add_63_sext
  v7_x23_add_63
  v7_fsp_1392_add_32
  v7_fsp_1264_add_137_sext
  v7_fsp_1264_add_137
  v7_fsp_1401_add_8
  v7_zext32_setWidth8
  v7_polyEncoderTag_bne_two
  v7_zext64_32_setWidth8
  v7_zext64_32_setWidth32
  v7_zext64_setWidth8
  v7_zext64_setWidth32_setWidth8

variable [LibsignalPlacement]

set_option maxHeartbeats 1200000 in
/-- When `<PolyEncoder>::from_pb` returns `.ok enc` at `fsp + 1888`, steps `+3720 -> +7260 -> +7348`,
moving `polyEncoderAt` from `fsp + 1888..2288` to `fsp + 1392..1792`, storing `p1` to `[sp, #0xc8]`
(`fsp + 200`) and `v7_polyEncoderTag enc` to `[sp, #0x10]` (`fsp + 16`), and setting `pstate` according
to `cmn x22, #0x1` (`addsPState64 cap_dec 1#64`). -/
theorem v7_enc_ok_move_3720_to_7348_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 p1 x21_val slot16_old slot200_old : BitVec 64)
    (enc : PolyEncoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 3720#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx20_1 : s1.readReg64 .x20 = fsp + 1792#64)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = fsp + 848#64)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx25_1 : s1.readReg64 .x25 = fsp + 1888#64)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hx28_1 : s1.readReg64 .x28 = p1)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7348#64) s1
      (stackAt fsp encoderFromPbStack ∗
        resultPolyEncoderFromPbAt A (fsp + 1888#64) (.ok enc) ∗
        memRegion (fsp + 1392#64) 400 ∗
        memRegion (fsp + 896#64) 56 ∗
        ((fsp + 16#64) ↦₆₄ slot16_old) ∗
        ((fsp + 200#64) ↦₆₄ slot200_old) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt fsp encoderFromPbStack ∗
          memRegion (fsp + 1888#64) 400 ∗
          polyEncoderAt A (fsp + 1392#64) enc ∗
          memRegion (fsp + 896#64) 56 ∗
          ((fsp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
          ((fsp + 200#64) ↦₆₄ p1) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = v7_polyEncoderTag enc ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = cap_dec ∧
        sm.readReg64 .x23 = fsp + 848#64 ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x25 = fsp + 1888#64 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.pstate = addsPState64 cap_dec 1#64 ∧
        TraceCalleeSaved sm s0) := by
  subst hsp1
  have hmemcpy : subroutine_ok ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      (lsρ EncoderFromPb.spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem hA.memcpy
  simp only [sessionMemcpySpec, allocHookStack, stackAt] at hmemcpy
  wp_conv_pre =>
    rw [v7_resultPolyEncoder_ok_eq, v7_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_polyEncoderAt_relocate_1888_to_1392 A s1.sp enc)
      (sepConj_mono (v7_memRegion_1392_400_split_32_368 s1.sp)
        (sepConj_mono_left (v7_memRegion_896_56_split_24_32 s1.sp))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d16
  apply ProofLib.SepWP.exists_left; intro d8
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro e24
  apply ProofLib.SepWP.exists_left; intro e16
  apply ProofLib.SepWP.exists_left; intro e8
  apply ProofLib.SepWP.exists_left; intro e0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro tail368
  apply ProofLib.SepWP.exists_left; intro P_heap
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    ⌜(((s1.sp + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 1400#64) ↦₆₄ w8) ∗
      ((s1.sp + 1408#64) ↦₆₄ w16) ∗
      ((s1.sp + 1416#64) ↦₆₄ w24) ∗
      ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗ P_heap ⊢
        polyEncoderAt A (s1.sp + 1392#64) enc)⌝ ∗
    (memRegion (s1.sp - 4096#64) 4096 ∗
     memRegion (s1.sp - 5152#64) 1056 ∗
     (((s1.sp + 1888#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 1896#64) ↦₆₄ w8) ∗
      ((s1.sp + 1904#64) ↦₆₄ w16) ∗
      ((s1.sp + 1912#64) ↦₆₄ w24) ∗
      ((s1.sp + 1920#64) ↦ₛ tail368.val) ∗
      P_heap) ∗
     (((s1.sp + 1392#64) ↦₆₄ e0) ∗
      ((s1.sp + 1400#64) ↦₆₄ e8) ∗
      ((s1.sp + 1408#64) ↦₆₄ e16) ∗
      ((s1.sp + 1416#64) ↦₆₄ e24) ∗
      memRegion (s1.sp + 1424#64) 368) ∗
     (((s1.sp + 896#64) ↦₆₄ d0) ∗
      ((s1.sp + 904#64) ↦₆₄ d8) ∗
      ((s1.sp + 912#64) ↦₆₄ d16) ∗
      memRegion (s1.sp + 920#64) 32) ∗
     ((s1.sp + 16#64) ↦₆₄ slot16_old) ∗
     ((s1.sp + 200#64) ↦₆₄ slot200_old) ∗
     Frame) by ac_rfl)) ?_
  apply ProofLib.SepWP.pure_elim; intro hreloc
  change s1.pc = (blkPl_333).base + 3720#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_333).base + 7348#64) s1 _ _
  wp_simp_pre [v7_fsp_1896_triple_rest, sepConj_assoc]
  wp_steps
  wp_simp_pre only [v7_fsp_1905_realign_rest, sepConj_assoc]
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_simp_pre only [v7_fsp_904_realign_rest, sepConj_assoc]
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  have hlen368 : (368 : Nat) = tail368.val.length := tail368.property.symm
  wp_simp_pre [hlen368, sepConj_assoc]
  wp_call hmemcpy (s1.sp + 1424#64, s1.sp + 1920#64, tail368.val)
  wp_simp_pre only [v7_fsp_904_unrealign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v7_fsp_904_realign_w24_rest, sepConj_assoc]
  wp_step
  wp_simp_pre [v7_fsp_1400_triple_rest, sepConj_assoc]
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_step
  wp_simp_pre only [v7_fsp_1409_realign_rest, sepConj_assoc]
  wp_step
  wp_simp_pre only [v7_fsp_904_unrealign_w24_rest, v7_1896_realign_final_rest, v7_1400_realign_final_rest, sepConj_assoc]
  refine EncoderFromPb.align_pre ?_ ?_
  · have h1888_400 := v7_1888_32_368_entails_memRegion_400 s1.sp (v7_polyEncoderTag enc) w8 w16 w24 tail368
    have h896_56 := v7_896_spill_entails_memRegion_56 s1.sp
      (unshiftWord w8 (loByte w16)) (unshiftWord w16 (loByte w24)) (w24 >>> 8) ((d16 >>> 56).setWidth 8)
    refine Entails.trans (Entails.of_eq (show _ =
      (memRegion (s1.sp - 4096#64) 4096 ∗ memRegion (s1.sp - 5152#64) 1056) ∗
      (((s1.sp + 1888#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       ((s1.sp + 1896#64) ↦₆₄ w8) ∗ ((s1.sp + 1904#64) ↦₆₄ w16) ∗
       ((s1.sp + 1912#64) ↦₆₄ w24) ∗ ((s1.sp + 1920#64) ↦ₛ tail368.val)) ∗
      (((s1.sp + 1392#64) ↦₆₄ v7_polyEncoderTag enc) ∗
       ((s1.sp + 1400#64) ↦₆₄ w8) ∗ ((s1.sp + 1408#64) ↦₆₄ w16) ∗
       ((s1.sp + 1416#64) ↦₆₄ w24) ∗ ((s1.sp + 1424#64) ↦ₛ tail368.val) ∗ P_heap) ∗
      (((s1.sp + 896#64) ↦₆₄ unshiftWord w8 (loByte w16)) ∗
       ((s1.sp + 904#64) ↦₆₄ unshiftWord w16 (loByte w24)) ∗
       (((s1.sp + 912#64) ↦ₛ EncoderFromPb.loBytes7 (w24 >>> 8)) ∗
        ((s1.sp + 919#64) ↦₈ (d16 >>> 56).setWidth 8)) ∗
       memRegion (s1.sp + 920#64) 32) ∗
      ((s1.sp + 16#64) ↦₆₄ v7_polyEncoderTag enc) ∗
      ((s1.sp + 200#64) ↦₆₄ p1) ∗
      Frame by ac_rfl)) ?_
    rw [← v7_stackAt_encoderFromPbStack_eq_allocHook s1.sp]
    exact sepConj_mono (Entails.refl _) (sepConj_mono h1888_400
      (sepConj_mono hreloc (sepConj_mono h896_56 (Entails.refl _))))
  · wp_done

/-- When `s.receivingEk = none` (`cap_dec = noneCap`, `s1.pstate = addsPState64 noneCap 1#64`),
steps `+7348 -> +10556`, drops `enc` at `fsp + 1392..1792`, deallocates all 5 vectors of `uc`
via `v7_cleanup_10556_placed`, and reaches `+4632`. -/
theorem v7_enc_ok_none_dec_7348_to_4632_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out pbA c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hpstate1 : s1.pstate = addsPState64 noneCap 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
        (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        (((pbA + 184#64) ↦₆₄ noneCap) ∗
         v7_optProtoPolyDecoderTail A (pbA + 184#64) noneCap none) ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
          (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          memRegion (pbA + 184#64) 40 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hm_dec :
      ((pbA + 184#64) ↦₆₄ noneCap) ∗
      v7_optProtoPolyDecoderTail A (pbA + 184#64) noneCap none ⊢
      memRegion (pbA + 184#64) 40 := by
    unfold v7_optProtoPolyDecoderTail
    exact optProtoPolyDecoder_none_entails_memRegion_40 (pbA + 184#64)
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono
        (v7_ct1SentHeap_entails_dealloc A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5)
        (sepConj_mono_left hm_dec))))))) ?_
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 10556#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
      (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
      (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      (vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2 ∗ vecCapPtrDealloc A c3 p3 ∗
       vecCapPtrDealloc A c4 p4 ∗ vecCapPtrDealloc A c5 p5) ∗
      memRegion (pbA + 184#64) 40 ∗
      A.pool ∗
      Frame)
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x24 = c2 ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 hpstate1 ⊢
    change s1.pc = (blkPl_333).base + 7348#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 10556#64) s1 _ _
    wp_steps
    wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, hx24_2, htr2⟩
    rw [v7_ct1SentWordsAt_1264_eq_spill_other]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.mono
        (v7_cleanup_10556_placed hA s0 s2 out c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 enc
          (v7_ct1SentOtherCells (s0.sp - 2400#64) c1 p1 l1 c2 l2 l3 l4 l5 uc.epoch ∗
           memRegion (pbA + 184#64) 40 ∗ Frame)
          hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 hx24_2 htr2) ?_)
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
       memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
       (((s0.sp - 2400#64) + 200#64) ↦₆₄ p1) ∗
       (((s0.sp - 2400#64) + 24#64) ↦₆₄ c1) ∗
       memRegion (pbA + 184#64) 40 ∗
       A.pool ∗
       Frame) by ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left h1264) (Entails.of_eq (by ac_rfl))

/-! ## 3. `<PolyDecoder>::from_pb` Copy (`+7348 -> +7400`) and Call (`+7400 -> lsmpl.base 376`) -/

set_option maxHeartbeats 800000 in
/-- Copy `ProtoPolynomialDecoder` (`40`B) from `pbA + 184` to `fsp + 1848` (`sp + 0x738`)
and set `x0 = fsp + 1888`, `x1 = fsp + 1848`, `x22 = fsp + 1888` at `+7348 -> +7400`. -/
theorem v7_copy_dec_7348_to_7400_placed
    {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA cap_dec c2 l1 x21_val x23_val : BitVec 64)
    (decPb : ProtoPolynomialDecoder) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hcap_dec : cap_dec.toNat < 2 ^ 63)
    (hpc1 : s1.pc = lsmpl.base 333 + 7348#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = cap_dec)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (hpstate1 : s1.pstate = addsPState64 cap_dec 1#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 7400#64) s1
      (((pbA + 184#64) ↦₆₄ cap_dec) ∗
        v7_optProtoPolyDecoderTail A (pbA + 184#64) cap_dec (some decPb) ∗
        memRegion (fsp + 1848#64) 40 ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          memRegion (pbA + 184#64) 40 ∗
          protoPolynomialDecoderAt A (fsp + 1848#64) decPb ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0) := by
  have hdec_ne := cap_add_one_beq_zero_false hcap_dec
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono (v7_decTail_unpack A (pbA + 184#64) cap_dec decPb)
      (sepConj_mono_left (v7_memRegion_1848_split_decCopy fsp)))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d32
  apply ProofLib.SepWP.exists_left; intro q9_hi
  apply ProofLib.SepWP.exists_left; intro q9_lo
  apply ProofLib.SepWP.exists_left; intro b8
  apply ProofLib.SepWP.exists_left; intro d0
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w16
  apply ProofLib.SepWP.exists_left; intro w24
  apply ProofLib.SepWP.exists_left; intro w32
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (v7_decTailWordsAt_to_step7352 pbA w8 w16 w24 w32))) ?_
  refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7360#64)
    (P_mid :=
      ((pbA + 184#64) ↦₆₄ cap_dec) ∗
      (((pbA + 192#64) ↦₆₄ w8) ∗
       ((pbA + 200#64) ↦₆₄ w16) ∗
       ((pbA + 208#64) ↦₆₄ w24) ∗
       ((pbA + 216#64) ↦₆₄ w32)) ∗
      v7_decTailHeap A cap_dec decPb w8 w16 w24 w32 ∗
      ((fsp + 1848#64) ↦₆₄ d0) ∗
      ((fsp + 1856#64) ↦₈ b8) ∗
      ((fsp + 1857#64) ↦₆₄ q9_lo) ∗
      ((fsp + 1865#64) ↦₆₄ q9_hi) ∗
      memRegion (fsp + 1873#64) 7 ∗
      ((fsp + 1880#64) ↦₆₄ d32) ∗
      Frame)
    (Q := fun sm =>
      sm.sp = fsp ∧
      sm.readReg64 .x8 = (EncoderFromPb.loByte w8).zeroExtend 64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = cap_dec ∧
      sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x26 = l1 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readVReg128 0#5 = (EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24) ++
        EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · change s1.pc = (blkPl_333).base + 7348#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 7360#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have htri_pb := (v7_triple64_to_byte_qword_tail7 (pbA + 192#64) w8 w16 w24).symm
      simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
        BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at htri_pb
      refine Entails.trans (Entails.of_eq (show _ =
        (((pbA + 192#64) ↦₈ EncoderFromPb.loByte w8) ∗
         ((pbA + 193#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
         ((pbA + 201#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
         ((pbA + 209#64) ↦ₛ EncoderFromPb.hiBytes7 w24)) ∗
        (((pbA + 184#64) ↦₆₄ cap_dec) ∗
         ((pbA + 216#64) ↦₆₄ w32) ∗
         v7_decTailHeap A cap_dec decPb w8 w16 w24 w32 ∗
         ((fsp + 1848#64) ↦₆₄ d0) ∗
         ((fsp + 1856#64) ↦₈ b8) ∗
         ((fsp + 1857#64) ↦₆₄ q9_lo) ∗
         ((fsp + 1865#64) ↦₆₄ q9_hi) ∗
         memRegion (fsp + 1873#64) 7 ∗
         ((fsp + 1880#64) ↦₆₄ d32) ∗
         Frame) by ac_rfl)) ?_
      rw [htri_pb]
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, hx8_2, hx19_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hq0_2, htr2⟩
    refine EncoderFromPb.seq_clean (mid := lsmpl.base 333 + 7392#64)
      (P_mid :=
        (∃∗ u16 : BitVec 64,
          ((fsp + 1856#64) ↦₆₄ w8) ∗
          ((fsp + 1864#64) ↦₆₄ w16) ∗
          ((fsp + 1872#64) ↦₆₄ u16)) ∗
        memRegion (pbA + 184#64) 40 ∗
        v7_decTailHeap A cap_dec decPb w8 w16 w24 w32 ∗
        ((fsp + 1848#64) ↦₆₄ cap_dec) ∗
        ((fsp + 1880#64) ↦₆₄ d32) ∗
        Frame)
      (Q := fun sm =>
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x8 = w24 ∧
        sm.readReg64 .x9 = w32 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        TraceCalleeSaved sm s0)
      ?_ ?_
    · change s2.pc = (blkPl_333).base + 7360#64 at hpc2
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7392#64) s2 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hpb_40 :
            ((pbA + 184#64) ↦₆₄ cap_dec) ∗
            ((pbA + 192#64) ↦₆₄ w8) ∗
            ((pbA + 200#64) ↦₆₄ w16) ∗
            ((pbA + 208#64) ↦₆₄ w24) ∗
            ((pbA + 216#64) ↦₆₄ w32) ⊢
            memRegion (pbA + 184#64) 40 := by
          have h := v7_decWordsAt_entails_40 (pbA + 184#64) cap_dec w8 w16 w24 w32
          unfold v7_decTailWordsAt at h
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h
          exact h
        have hfsp_q := v7_byte_qword_mem7_to_triple64 (fsp + 1856#64) w8 w16 w24
        simp only [pointsTo128, extractLsb'_0_64_append, extractLsb'_64_64_append,
          BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hfsp_q
        refine Entails.trans (Entails.of_eq (show _ =
          (((fsp + 1856#64) ↦₈ EncoderFromPb.loByte w8) ∗
           ((fsp + 1857#64) ↦₆₄ EncoderFromPb.unshiftWord w8 (EncoderFromPb.loByte w16)) ∗
           ((fsp + 1865#64) ↦₆₄ EncoderFromPb.unshiftWord w16 (EncoderFromPb.loByte w24)) ∗
           memRegion (fsp + 1873#64) 7) ∗
          ((((pbA + 184#64) ↦₆₄ cap_dec) ∗
            ((pbA + 192#64) ↦₆₄ w8) ∗
            ((pbA + 200#64) ↦₆₄ w16) ∗
            ((pbA + 208#64) ↦₆₄ w24) ∗
            ((pbA + 216#64) ↦₆₄ w32)) ∗
           (v7_decTailHeap A cap_dec decPb w8 w16 w24 w32 ∗
            ((fsp + 1848#64) ↦₆₄ cap_dec) ∗
            ((fsp + 1880#64) ↦₆₄ d32) ∗
            Frame)) by ac_rfl)) ?_
        exact sepConj_mono hfsp_q (sepConj_mono_left hpb_40)
      · wp_done
    · intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx8_3, hx9_3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx27_3, htr3⟩
      wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro u16
      change s3.pc = (blkPl_333).base + 7392#64 at hpc3
      change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
        ((blkPl_333).base + 7400#64) s3 _ _
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hpack := v7_decAt_pack A (fsp + 1848#64) cap_dec decPb w8 w16 w24 w32
        unfold v7_decTailWordsAt at hpack
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpack
        refine Entails.trans (Entails.of_eq (show _ =
          memRegion (pbA + 184#64) 40 ∗
          (((fsp + 1848#64) ↦₆₄ cap_dec) ∗
           (((fsp + 1856#64) ↦₆₄ w8) ∗
            ((fsp + 1864#64) ↦₆₄ w16) ∗
            ((fsp + 1872#64) ↦₆₄ w24) ∗
            ((fsp + 1880#64) ↦₆₄ w32)) ∗
           v7_decTailHeap A cap_dec decPb w8 w16 w24 w32) ∗
          Frame by ac_rfl)) ?_
        exact sepConj_mono_right (sepConj_mono_left hpack)
      · wp_done

/-- Step the `bl` instruction at `+7400` to `<PolyDecoder>::from_pb` entry (`lsmpl.base 376`). -/
theorem v7_bl_decoder_7400_to_35448_placed
    {ext : String → Option (State → State)}
    (s0 s1 : State) (fsp out pbA c2 l1 x21_val x23_val : BitVec 64)
    (P : SepProp)
    (hpc1 : s1.pc = lsmpl.base 333 + 7400#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx0_1 : s1.readReg64 .x0 = fsp + 1888#64)
    (hx1_1 : s1.readReg64 .x1 = fsp + 1848#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (hx21_1 : s1.readReg64 .x21 = x21_val)
    (hx22_1 : s1.readReg64 .x22 = fsp + 1888#64)
    (hx23_1 : s1.readReg64 .x23 = x23_val)
    (hx24_1 : s1.readReg64 .x24 = c2)
    (hx26_1 : s1.readReg64 .x26 = l1)
    (hx27_1 : s1.readReg64 .x27 = pbA)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 376) s1 P
      (fun sm Pm =>
        (Pm ⊢ P) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = fsp + 1888#64 ∧
        sm.readReg64 .x1 = fsp + 1848#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x21 = x21_val ∧
        sm.readReg64 .x22 = fsp + 1888#64 ∧
        sm.readReg64 .x23 = x23_val ∧
        sm.readReg64 .x24 = c2 ∧
        sm.readReg64 .x26 = l1 ∧
        sm.readReg64 .x27 = pbA ∧
        sm.readReg64 .x30 = lsmpl.base 333 + 7404#64 ∧
        TraceCalleeSaved sm s0) := by
  change s1.pc = (blkPl_333).base + 7400#64 at hpc1
  change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
    ((blkPl_376).base) s1 P
    (fun sm Pm =>
      (Pm ⊢ P) ∧
      sm.sp = fsp ∧
      sm.readReg64 .x0 = fsp + 1888#64 ∧
      sm.readReg64 .x1 = fsp + 1848#64 ∧
      sm.readReg64 .x19 = out ∧
      sm.readReg64 .x21 = x21_val ∧
      sm.readReg64 .x22 = fsp + 1888#64 ∧
      sm.readReg64 .x23 = x23_val ∧
      sm.readReg64 .x24 = c2 ∧
      sm.readReg64 .x26 = l1 ∧
      sm.readReg64 .x27 = pbA ∧
      sm.readReg64 .x30 = (blkPl_333).base + 7404#64 ∧
      TraceCalleeSaved sm s0)
  wp_steps
  wp_done

alias v7_copy_dec_7352_to_7400_placed := v7_copy_dec_7348_to_7400_placed

/-! ## 4. `<PolyDecoder>::from_pb = Err` Cleanup (`+7404 -> +11096 -> +4632`) -/

/-- When `<PolyDecoder>::from_pb` returns `.error err` at `fsp + 1888`, steps `+7404 -> +11096`,
drops `enc` (`fsp + 1392..1792`) and `uc` (`fsp + 1264..1392`) via `v7_cleanup_11096_placed`, and reaches `+4632`. -/
theorem v7_dec_err_7404_to_4632_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : FromPbAllocHooks A ext)
    (s0 s1 : State) (out c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (enc : PolyEncoder) (err : PolynomialError) (Frame : SepProp)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 333 + 7404#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 2400#64)
    (hx19_1 : s1.readReg64 .x19 = out)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_333 (Rust.withPanics ext))
      (lsmpl.base 333 + 4632#64) s1
      (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
        resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
        polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
        v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
        v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ∗
        A.pool ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
          memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1392#64) 400 ∗
          memRegion ((s0.sp - 2400#64) + 1264#64) 128 ∗
          A.pool ∗
          Frame) ∧
        sm.sp = s0.sp - 2400#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x28 = 0#64 ∧
        TraceCalleeSaved sm s0) := by
  have hpack_uc :
      v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
      v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 ⊢
      unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc := by
    rw [← v7_ct1SentAt_eq_unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc]
    exact v7_ct1SentAt_pack A ((s0.sp - 2400#64) + 1264#64) uc
      c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5
  refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (show _ =
    resultPolyDecoderFromPbAt A ((s0.sp - 2400#64) + 1888#64) (.error err) ∗
    (v7_ct1SentWordsAt ((s0.sp - 2400#64) + 1264#64) c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5 uc.epoch ∗
     v7_ct1SentHeap A uc c1 p1 l1 c2 p2 l2 c3 p3 l3 c4 p4 l4 c5 p5 l5) ∗
    (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
     polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
     A.pool ∗ Frame) by ac_rfl))
    (sepConj_mono (v7_resultPolyDecoder_err_entails_tag_392 A (s0.sp - 2400#64) err)
      (sepConj_mono_left hpack_uc))) ?_
  refine seq_clean_lscl hcl1
    (mid := lsmpl.base 333 + 11096#64)
    (P_mid :=
      stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
      polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
      unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc ∗
      A.pool ∗
      (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame))
    (Q := fun sm =>
      sm.sp = s0.sp - 2400#64 ∧
      sm.readReg64 .x19 = out ∧
      TraceCalleeSaved sm s0)
    ?_ ?_
  · dsimp only [noneCap, BitVec.ofNat_eq_ofNat] at hpc1 ⊢
    change s1.pc = (blkPl_333).base + 7404#64 at hpc1
    change SepWP ((blkPC_333).rebase (blkPl_333).base (Rust.withPanics ext))
      ((blkPl_333).base + 11096#64) s1 _ _
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · have hm400 := v7_1888_tag_392_to_memRegion_400 (s0.sp - 2400#64) 18446744073709551615#64
      refine Entails.trans (Entails.of_eq (show _ =
        ((((s0.sp - 2400#64) + 1888#64) ↦₆₄ 18446744073709551615#64) ∗
         memRegion ((s0.sp - 2400#64) + 1896#64) 392) ∗
        (stackAt (s0.sp - 2400#64) encoderFromPbStack ∗
         polyEncoderAt A ((s0.sp - 2400#64) + 1392#64) enc ∗
         unchunkedCt1SentAt A ((s0.sp - 2400#64) + 1264#64) uc ∗
         A.pool ∗
         Frame) by ac_rfl)) ?_
      exact Entails.trans (sepConj_mono_left hm400) (Entails.of_eq (by ac_rfl))
    · wp_done
  · intro s2 hpc2 hrun2 hcl2 ⟨hsp2, hx19_2, htr2⟩
    refine SepWP.mono
      (v7_cleanup_11096_placed hA s0 s2 out enc uc
        (memRegion ((s0.sp - 2400#64) + 1888#64) 400 ∗ Frame)
        hcl2 hsp0_align hpc2 hrun2 hsp2 hx19_2 htr2) ?_
    intro s3 P3 hrun3 hpc3 ⟨hP3, hq⟩
    exact ⟨Entails.trans hP3 (Entails.of_eq (by ac_rfl)), hq⟩

end CryptoVerification.SpqrV1.States.FromPb
