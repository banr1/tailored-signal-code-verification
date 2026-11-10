/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4Ext
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4b
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 4b (`AllocContracts4K`: Arm 6 `headerReceived`)

Lifts `states_into_pb_headerReceived` (Arm 6, tag `8`) from stackless
`sessionMemcpyRegionSpec` to 4-KiB stack-framed `SpqrV1.Alloc.AllocContracts4K`.
-/

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bExt

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.CodeLayout
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (spqrPolyApi spqrAuthApi)
open CryptoVerification.SpqrV1.Alloc (AllocContracts4K)
open CryptoVerification.SpqrV1.Poly (polyDecoderAt protoPolynomialDecoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.DecoderPb (DecoderIntoPbOkExt)
open CryptoVerification.SpqrV1.Drop (optProtoInnerStateSize chunkedStatesAt)
open CryptoVerification.SpqrV1.States.IntoPb
  (bv_sub_sub_lit' bv_add_add_lit' statesIntoPbName statesIntoPbVariantSpec
   statesIntoPbStack statesIntoPbJumpTableAt statesIntoPbSavedCells
   authenticatorHeap vecU8Heap sub_ok_decoderIntoPb_raw sub_ok_memcpy_4k_raw
   sepWPp_of_states_into_pb_wpp statesIntoPb_seq_sepWP states_into_pb_prologue_60
   call_memcpy_keep_relocate_4k call_decoderIntoPb_expose Relocatable
   chunkedHeaderReceived_expose stack_1416_split_headerReceived
   states_into_pb_headerReceived_pre1 states_into_pb_headerReceived_pre2
   states_into_pb_headerReceived_post)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'

set_option maxHeartbeats 800000 in
/-- Verifies `<States>::into_pb` on `.headerReceived s` (Arm 6, tag `8`)
under `AllocContracts4K`. -/
theorem states_into_pb_headerReceived_4k {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hdec : DecoderIntoPbOkExt b A ext)
    (hA : AllocContracts4K b A ext)
    (s : CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived
      spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesIntoPbName)
      (statesIntoPbVariantSpec A F b (.headerReceived s)) := by
  have hdec_raw := sub_ok_decoderIntoPb_raw hdec
  have hmemcpy_raw := sub_ok_memcpy_4k_raw hA
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
    exact Entails.of_eq (by sep_ac_rfl)
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
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
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
  refine call_memcpy_keep_relocate_4k hmemcpy_raw
    (k := 72) (m := 408) (n := 480) (off := 72#64)
    (F := F_words) (G := G_dec)
    rfl rfl
    (Relocatable.words9 a0 a1 a2 a3 a4 a5 h0 h1 h2)
    (Relocatable.epoch_polyDecoderAt A s.uc.epoch s.receiving_ek)
    (s0.sp - 1360#64) (stA + 8#64)
    (Frame :=
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
    (by rw [hF_src, hG_src]; sep_ac_rfl)
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
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
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
    (by sep_ac_rfl)
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
  sep_ac_rfl

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bExt

-- AUTO-BRIDGE BEGIN
namespace CryptoVerification.SpqrV1.States.IntoPb
export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4bExt
  (states_into_pb_headerReceived_4k)
end CryptoVerification.SpqrV1.States.IntoPb
-- AUTO-BRIDGE END
