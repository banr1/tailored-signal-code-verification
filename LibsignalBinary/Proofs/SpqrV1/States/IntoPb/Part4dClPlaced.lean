/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4dPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4ClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.NoHeaderReceivedClPlaced
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4d
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` (Block `334`) — Part 4d `withLsCodeLoaded`: Arm 2 (`States.headerSent`)

Relocatable `[LibsignalPlacement]` verification of Arm 2 (`States.headerSent`, tag `4`) with
`withLsCodeLoaded` on `<PolyEncoder>::into_pb` (Block `375`), `<PolyDecoder>::into_pb` (Block `377`),
and Block `334`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.IntoPb

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
open CryptoVerification.SpqrV1.Poly.DecoderPb
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open LibsignalPublicApi.StoreKit

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

set_option maxHeartbeats 800000 in
/-- Verifies `<States>::into_pb` (Block `334`) on `.headerSent s` (Arm 2, tag `4`)
    with `withLsCodeLoaded` on `<PolyEncoder>::into_pb` (`Block 375`), `<PolyDecoder>::into_pb`
    (`Block 377`), and Block `334`. -/
theorem states_into_pb_headerSent_cl_placed [LibsignalPlacement] {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (henc_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A)))
    (hdec_cl : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A)))
    (hmemcpy_raw : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec)
    (s : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeLoaded lsmpl (statesIntoPbVariantPlacedSpec A F (.headerSent s))) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨out, stA⟩ R s0 hpc hrun hpre hsp0_align
  obtain ⟨hcl0, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [statesIntoPbVariantPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0⟩, hmem⟩
  refine ⟨memRegion out optProtoInnerStateSize ∗
      chunkedStatesAt A stA (.headerSent s) ∗
      statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack,
    R, ?_, ?_⟩
  · simpa [sepConj_assoc] using hmem
  refine sepWPp_of_states_into_pb_wpp_placed s0 s0 out stA (.headerSent s) _ R ?_
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
        statesIntoPbJumpTablePlacedAt ∗ A.pool ∗ stackAt s0.sp statesIntoPbStack ⊢
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
         memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt ∗ A.pool) := by
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
  have hpro := states_into_pb_prologue_60_placed (ext := ext) s0 out stA 4#64
    (polyEncoderAt A (stA + 8#64) s.sending_ek ∗
     (((stA + 408#64) ↦₆₄ a0) ∗ ((stA + 416#64) ↦₆₄ a1) ∗ ((stA + 424#64) ↦₆₄ a2) ∗
      ((stA + 432#64) ↦₆₄ a3) ∗ ((stA + 440#64) ↦₆₄ a4) ∗ ((stA + 448#64) ↦₆₄ a5) ∗
      ((stA + 456#64) ↦₆₄ k0) ∗ ((stA + 464#64) ↦₆₄ k1) ∗ ((stA + 472#64) ↦₆₄ k2)) ∗
     (((stA + 480#64) ↦₆₄ s.uc.epoch) ∗ polyDecoderAt A (stA + 488#64) s.receiving_ct1) ∗
     authenticatorHeap A a0 a1 a2 a3 a4 a5 s.uc.auth ∗ vecU8Heap A k0 k1 k2 s.uc.dk ∗
     memRegion (stA + 888#64) 40 ∗ memRegion out optProtoInnerStateSize ∗
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hsp0_align hpc hrun hx8 hx0
  refine statesIntoPb_seq_sepWP_cl hcl0 hpro fun s1 hpc1 hrun1 hcl1
    ⟨hsp1, hx29_1, hx28_1, hx27_1, hx26_1, hx20_1, hx19_1, hx8_1, htr1⟩ => ?_
  rw [stack_1416_split_headerSent s0.sp]
  have hpre1 := states_into_pb_headerSent_pre1_placed (ext := ext) s0 s1 out stA
    hsp0_align hpc1 hrun1 hsp1 hx29_1 hx28_1 hx27_1 hx26_1 hx20_1 hx19_1 hx8_1 htr1
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
    (statesIntoPb_seq_sepWP_cl hcl1 hpre1 fun s2 hpc2 hrun2 hcl2
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
  refine call_memcpy_keep_relocate_cl hmemcpy_raw
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
      statesIntoPbJumpTablePlacedAt ∗ A.pool)
    hcl2 hpc2 hrun2 hsp2 hfsp_align hlr2 htr2 hx0_2 hx1_2 hx2_2
    (by rw [hF_src, hG_src]; ac_rfl)
    fun s3 hpc3 hrun3 hsp3 hcs3 htr3 hcl3 => ?_
  rw [hF_src, hG_dst, hsrc_off]
  have hx19_3 : s3.readReg64 .x19 = out := hcs3.1.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = stA := hcs3.2.1.trans hx20_2
  have hx21_3 : s3.readReg64 .x21 = s0.sp - 1360#64 := hcs3.2.2.1.trans hx21_2
  have hx22_3 : s3.readReg64 .x22 = (1#64 <<< 63 ||| 2#64) := hcs3.2.2.2.1.trans hx22_2
  have hx26_3 : s3.readReg64 .x26 = s0.sp - 480#64 := hcs3.2.2.2.2.2.2.2.1.trans hx26_2
  have hx28_3 : s3.readReg64 .x28 = s0.sp - 256#64 := hcs3.2.2.2.2.2.2.2.2.2.1.trans hx28_2
  have hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64 := hcs3.2.2.2.2.2.2.2.2.2.2.1.trans hx29_2
  have hpre2 := states_into_pb_headerSent_pre2_placed (ext := ext) s0 s3 out stA
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
     statesIntoPbJumpTablePlacedAt ∗ A.pool)
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (statesIntoPb_seq_sepWP_cl hcl3 hpre2 fun s4 hpc4 hrun4 hcl4
      ⟨hsp4, hlr4, hx0_4, hx1_4, hx29_4, hx26_4, hx24_4, hx23_4, hx22_4, hx21_4, hx19_4, htr4⟩ => ?_)
  refine call_encoderIntoPb_expose_cl_placed henc_cl (s0.sp - 400#64) (stA + 8#64) s.sending_ek
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
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hcl4 hpc4 hrun4 hsp4 hfsp_align hlr4 htr4 hx0_4 hx1_4
    (by ac_rfl)
    fun s5 e0 e1 e2 e3 e4 e5 e6 hpc5 hrun5 hsp5 hcs5 htr5 hcl5 => ?_
  have hx19_5 : s5.readReg64 .x19 = out := hcs5.1.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = s0.sp - 1360#64 := hcs5.2.2.1.trans hx21_4
  have hx22_5 : s5.readReg64 .x22 = (1#64 <<< 63 ||| 2#64) := hcs5.2.2.2.1.trans hx22_4
  have hx23_5 : s5.readReg64 .x23 = s.uc.epoch := hcs5.2.2.2.2.1.trans hx23_4
  have hx24_5 : s5.readReg64 .x24 = s0.sp - 480#64 := hcs5.2.2.2.2.2.1.trans hx24_4
  have hx26_5 : s5.readReg64 .x26 = s0.sp - 480#64 := hcs5.2.2.2.2.2.2.2.1.trans hx26_4
  have hx29_5 : s5.readReg64 .x29 = s0.sp - 96#64 := hcs5.2.2.2.2.2.2.2.2.2.2.1.trans hx29_4
  have hpre3 := states_into_pb_headerSent_pre3_placed (ext := ext) s0 s5 out s.uc.epoch
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
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt))
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]))
    (statesIntoPb_seq_sepWP_cl hcl5 hpre3 fun s6 hpc6 hrun6 hcl6
      ⟨hsp6, hlr6, hx0_6, hx1_6, hx29_6, hx26_6, hx23_6, hx22_6, hx19_6, htr6⟩ => ?_)
  refine call_decoderIntoPb_expose_cl_placed hdec_cl (s0.sp - 344#64) (s0.sp - 880#64) s.receiving_ct1
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
      memRegion out optProtoInnerStateSize ∗ statesIntoPbJumpTablePlacedAt)
    hcl6 hpc6 hrun6 hsp6 hfsp_align hlr6 htr6 hx0_6 hx1_6
    (by ac_rfl)
    fun sf d0 d1 d2 d3 d4 hpcf hrunf hspf hcsf htrf => ?_
  have hx19_f : sf.readReg64 .x19 = out := hcsf.1.trans hx19_6
  have hx22_f : sf.readReg64 .x22 = (1#64 <<< 63 ||| 2#64) := hcsf.2.2.2.1.trans hx22_6
  have hx23_f : sf.readReg64 .x23 = s.uc.epoch := hcsf.2.2.2.2.1.trans hx23_6
  have hx26_f : sf.readReg64 .x26 = s0.sp - 480#64 := hcsf.2.2.2.2.2.2.2.1.trans hx26_6
  have hx29_f : sf.readReg64 .x29 = s0.sp - 96#64 := hcsf.2.2.2.2.2.2.2.2.2.2.1.trans hx29_6
  apply SepWPp.of_sepWP_ret
  have hpost_step := states_into_pb_headerSent_post_placed (ext := ext) A F s0 sf out stA s
    a0 a1 a2 a3 a4 a5 k0 k1 k2 e0 e1 e2 e3 e4 e5 e6 d0 d1 d2 d3 d4
    hsp0_align hpcf hrunf hspf hx29_f hx26_f hx23_f hx22_f hx19_f htrf
  refine SepWP.weaken_pre (Entails.of_eq ?_) hpost_step
  simp only [arm64_norm]
  ac_rfl

end CryptoVerification.SpqrV1.States.IntoPb
