/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueB
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepX
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32ArmsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` Unified Prologue and Decode Loop

Proves the empty-body error path (`+0x0bc → +0x504`), loop entry (`+0x0bc → +0x0f4`), unified
prologue theorems (`+0x000 → +0x504` / `+0x460`), and fuel-inducted protobuf decode loop on
`preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs PreKeyLoopRegs.of_calleeSaved SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

private abbrev of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
attribute [local simp, local arm64_norm, local wp_norm]
  cond_eq_subs1_false_w40 cond_eq_len1

/-! ## 1. Pure Frame Splitting/Packing Helpers for `prologue_bc_len1_to_504_placed_wpE` -/

private theorem lsw_memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ s104 : BitVec 64, ∃∗ s96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (16 + 184) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 96#64)))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem lsw_memRegion296_pack (sp' s96 s104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
    memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    Prost.memRegion_split sp' 96 200 (by decide),
    Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

private theorem lsw_initCells_to_full (sp' : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
    ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
    ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
    ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
    ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
    ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
    ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
    ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ⊢
      ∃∗ u436 : BitVec 32, ∃∗ u428 : BitVec 32, ∃∗ u420 : BitVec 32, ∃∗ u412 : BitVec 32,
      ∃∗ msgLen : BitVec 64, ∃∗ msgPtr : BitVec 64,
      ∃∗ ikLen : BitVec 64, ∃∗ ikPtr : BitVec 64,
      ∃∗ bkLen : BitVec 64, ∃∗ bkPtr : BitVec 64,
      ∃∗ kyberLen : BitVec 64, ∃∗ kyberPtr : BitVec 64,
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) := by
  have hm4 (a : BitVec 64) : memRegion a 4 = (∃∗ u : BitVec 32, a ↦₃₂ u) :=
    ProofLib.memRegion_four a
  rw [hm4 (sp' + 412#64), hm4 (sp' + 420#64), hm4 (sp' + 428#64), hm4 (sp' + 436#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 320#64))
      (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 344#64))
        (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 368#64))
          (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 392#64)))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem lsw_full_cells_memRegion128 (sp' : BitVec 64)
    (w312 kyberPtr kyberLen w336 bkPtr bkLen w360 ikPtr ikLen w384 msgPtr msgLen : BitVec 64)
    (u408 u412 u416 u420 u424 u428 u432 u436 : BitVec 32) :
    ((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
    ((sp' + 328#64) ↦₆₄ kyberLen) ∗
    ((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
    ((sp' + 352#64) ↦₆₄ bkLen) ∗
    ((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
    ((sp' + 376#64) ↦₆₄ ikLen) ∗
    ((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
    ((sp' + 400#64) ↦₆₄ msgLen) ∗
    ((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
    ((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
    ((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
    ((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436) ⊢
      memRegion (sp' + 312#64) 128 := by
  have hw24 (a w0 w1 w2 : BitVec 64) :
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide,
      Prost.memRegion_split a 8 16 (by decide),
      Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hu8 (a : BitVec 64) (v0 v4 : BitVec 32) :
      (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v4) ⊢ memRegion a 8 := by
    rw [show (8 : Nat) = 4 + 4 by decide, Prost.memRegion_split a 4 4 (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _)
  have h312 := hw24 (sp' + 312#64) w312 kyberPtr kyberLen
  have h336 := hw24 (sp' + 336#64) w336 bkPtr bkLen
  have h360 := hw24 (sp' + 360#64) w360 ikPtr ikLen
  have h384 := hw24 (sp' + 384#64) w384 msgPtr msgLen
  have h408 := hu8 (sp' + 408#64) u408 u412
  have h416 := hu8 (sp' + 416#64) u416 u420
  have h424 := hu8 (sp' + 424#64) u424 u428
  have h432 := hu8 (sp' + 432#64) u432 u436
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h312 h336 h360 h384 h408 h416 h424 h432
  rw [show (128 : Nat) = 24 + (24 + (24 + (24 + (8 + (8 + (8 + 8)))))) by decide,
    Prost.memRegion_split (sp' + 312#64) 24 104 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64) 24 80 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64) 24 56 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64) 24 32 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64) 8 24 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp' + 312#64 + 24#64 + 24#64 + 24#64 + 24#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (Q :=
      (((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen)) ∗
      (((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen)) ∗
      (((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen)) ∗
      (((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen)) ∗
      (((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412)) ∗
      (((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420)) ∗
      (((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428)) ∗
      (((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono h312 (sepConj_mono h336 (sepConj_mono h360 (sepConj_mono h384
    (sepConj_mono h408 (sepConj_mono h416 (sepConj_mono h424 h432))))))

private theorem lsw_region152_repack (sp' c0 c1 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ c0) ∗ ((sp' + 304#64) ↦₆₄ c1) ∗
      memRegion (sp' + 312#64) 128 ∗ ((sp' + 440#64) ↦₆₄ w440) ⊢
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (128 + 8)) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _) (pointsTo64_entails_memRegion _ _)))

/-! ## 2. `prologue_bc_len1_to_504_placed_wpE` and `prologue_bc_gt1_to_f4_placed_wpX` -/

theorem prologue_bc_len1_to_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {sret sp' ptr : BitVec 64} {s0 s3 : State}
    (hst : PostEpilogueStatePlaced s0 sp' s3)
    (hpc : s3.pc = (blkPl_111).base + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 1#64 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx19 : s3.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s3
      (memRegion sret 248 ∗
        memRegion sp' 296 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗
        ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)))
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ pksmErrE A [] sret .invalidProtobufEncoding ∗
          memRegion sp' 296 ∗
          memRegion (sp' + 296#64) 152))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (lsw_memRegion296_split sp')
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (lsw_initCells_to_full sp')))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun u436 => SepWPp.exists_pre fun u428 =>
    SepWPp.exists_pre fun u420 => SepWPp.exists_pre fun u412 =>
    SepWPp.exists_pre fun msgLen => SepWPp.exists_pre fun msgPtr =>
    SepWPp.exists_pre fun ikLen => SepWPp.exists_pre fun ikPtr =>
    SepWPp.exists_pre fun bkLen => SepWPp.exists_pre fun bkPtr =>
    SepWPp.exists_pre fun kyberLen => SepWPp.exists_pre fun kyberPtr =>
    SepWPp.exists_pre fun s104 => SepWPp.exists_pre fun s96 => ?_
  refine SepWPp.mono_pre
    (P' := (((sp' + 104#64) ↦₆₄ s104) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr)) ∗
      (memRegion sret 248 ∗
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_entails
    (prologue_bc_len1_to_524_placed_wpX hst hpc hrun hpstate hx29 hx27 hx19) ?_
  intro s4 hpc4 hrun4 ⟨hst4, hx29_4, hx28_4, hx27_4, hx26_4, hx23_4, hx19_4, _, hx1_4⟩
  refine SepWPp.mono_pre
    (P' := (memRegion sret 248 ∗
        ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
        ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
      (memRegion sp' 96 ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (prologue_524_len1_to_504_placed_wpE (A := A) hst4 hpc4 hrun4 hx29_4 hx28_4 hx27_4 hx26_4 hx23_4 hx19_4 hx1_4) ?_
  intro sf Pf ⟨hstf, hentf⟩
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  have hm296 := lsw_memRegion296_pack sp' (s4.readReg64 .x8) ikPtr
  have hm128 := lsw_full_cells_memRegion128 sp'
    0x8000000000000002#64 kyberPtr kyberLen noneCap bkPtr bkLen noneCap ikPtr ikLen noneCap msgPtr msgLen
    0#32 u412 0#32 u420 0#32 u428 0#32 u436
  have hm152 := lsw_region152_repack sp' (ptr + 1#64) 0#64 (sp' + 296#64)
  refine Entails.trans (Q := pksmErrE A [] sret .invalidProtobufEncoding ∗
      (memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184) ∗
      (((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
          ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
          ((sp' + 352#64) ↦₆₄ bkLen) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
          ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗
          ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine sepConj_mono_right (sepConj_mono hm296 ?_)
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm128)))
    (by simpa [sepConj_assoc] using hm152)

theorem prologue_bc_gt1_to_f4_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {sret sp' ptr : BitVec 64} {vb : BitVec 8} {n : Nat}
    {s0 s3 : State}
    (hge2 : 2 ≤ n) (hlt : n < 2 ^ 32)
    (hst : PostEpilogueStatePlaced s0 sp' s3)
    (hpc : s3.pc = (blkPl_111).base + 188#64)
    (hrun : s3.status = .Running)
    (hpstate : s3.pstate = subsPState64 (BitVec.ofNat 64 n) 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64)
    (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s3.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s3.readReg64 .x21 = ptr)
    (hx20 : s3.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx19 : s3.readReg64 .x19 = sret)
    (hx8 : s3.readReg64 .x8 = sp' + 296#64)
    (hx2 : s3.readReg64 .x2 = BitVec.ofNat 64 n - 1#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 244#64) s3
      emp
      (fun s4 P4 =>
        (PreKeyLoopRegs sp' sret (BitVec.ofNat 64 n) ptr vb s4 ∧
        PostEpilogueStatePlaced s0 sp' s4 ∧
        s4.readReg64 .x28 = sp' + 296#64 ∧
        s4.readReg64 .x26 = sp' + 304#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 n - 1#64) ∧
        (P4 ⊢ emp))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond_eq := cond_eq_subs1_false_w40 hge2 hlt
  refine of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl4 => ?_
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
    by simp [hx27, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩,
    ⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
      hcl4, by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [hx2, arm64_norm]⟩, Entails.refl _⟩

/-! ## 3. `PreKeyDecodeLoopF4OkWPlaced` & Unified Prologue Theorems -/

def PreKeyDecodeLoopF4OkWPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  ∀ (s0 : State) (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (fuel : Nat) (s : State)
    (ptr : BitVec 64) (b0 : BitVec 8) (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage),
    s.pc = (blkPl_111).base + 0x0f4#64 →
    s.status = .Running →
    PreKeyLoopRegs sp' sret len ptr0 vb s →
    s.readReg64 .x28 = sp' + 296#64 → s.readReg64 .x26 = sp' + 304#64 →
    s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
    s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
    (b0 :: bs1).length ≤ fuel + 1 → (b0 :: bs1).length < 2 ^ 32 →
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0)

private theorem lsw_ofNat64_cons_sub_one (b0 : BitVec 8) (bs : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs).length - 1#64 = BitVec.ofNat 64 bs.length := by
  simp only [List.length_cons]; bv_omega

theorem preKey_init_to_460_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced A H)
    {sret sp' ptr : BitVec 64} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)}
    {s0 s2 : State}
    (hlt : (vb :: b1 :: bs1).length < 2 ^ 32)
    (hst : PostEpilogueStatePlaced s0 sp' s2)
    (hpc : s2.pc = (blkPl_111).base + 128#64)
    (hrun : s2.status = .Running)
    (hx29 : s2.readReg64 .x29 = sp' + 512#64)
    (hx27 : s2.readReg64 .x27 = 0x8000000000000002#64)
    (hx22 : s2.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s2.readReg64 .x21 = ptr)
    (hx19 : s2.readReg64 .x19 = sret)
    (hx1 : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1120#64) s2
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗ memRegion (sp' + 296#64) 152 ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (preKeyLoopExitPostPlaced A s0 sp' sret
        (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
        (ptr + 1#64) (b1 :: bs1) (Pksm.decodeProto (b1 :: bs1)))
      (tryFromQp s0) := by
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 296#64) 152 ∗
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (prologue_80_init_placed_wpX hst hpc hrun hx29 hx27 hx22 hx21 hx19 hx1) ?_
  intro s3 P3 hpc3 hrun3
    ⟨hst3, hpstate3, hx29_3, hx27_3, hx22_3, hx21_3, hx20_3, hx19_3, hx8_3, hx2_3, hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_; clear hent3
  have hge2 : 2 ≤ (vb :: b1 :: bs1).length := by simp
  have hsub1 := lsw_ofNat64_cons_sub_one vb (b1 :: bs1)
  have hwire := emptyPreKey_cells_entails_wirePreKeyOf A (sp' + 312#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hwire
  refine SepWPp.mono_pre
    (P' := emp ∗ (sliceCursorAt (sp' + 296#64) (ptr + 1#64) (b1 :: bs1) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ memRegion (sp' + 448#64) 64 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
      wirePreKeyOf A (sp' + 312#64) Pksm.emptyProto))
    (by
      rw [emp_sepConj]; unfold sliceCursorAt; rw [hsub1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hwire)))))
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_entails
    (prologue_bc_gt1_to_f4_placed_wpX hge2 hlt hst3 hpc3 hrun3
      hpstate3 hx29_3 hx27_3 hx22_3 hx21_3 hx20_3 hx19_3 hx8_3 hx2_3) ?_
  intro s4 hpc4 hrun4 ⟨hregs4, ⟨_, hsp4, hcl4, htr4⟩, hx28_4, hx26_4, hx2_4⟩
  rw [hsub1] at hx2_4
  have hlt_body : (b1 :: bs1).length < 2 ^ 32 := by simp only [List.length_cons] at hlt ⊢; omega
  simpa [Pksm.decodeProto] using hLoopF4 s0 sp' sret (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
    bs1.length s4 (ptr + 1#64) b1 bs1 Pksm.emptyProto
    hpc4 hrun4 hregs4 hx28_4 hx26_4 hx2_4 hsp4 hcl4 htr4 (Nat.le_refl _) hlt_body

theorem preKey_earlyErr_to_504_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State}
    (herr : x.bytes = [] ∨
      (∃ vb body, x.bytes = vb :: body ∧
        ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96)
      (fun sf Pf =>
        PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧
        Pksm.pksmParse x.bytes = none ∧
        ∃ e : SignalProtocolError,
          Pf ⊢ pksmErrE A [] x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗
            memRegion (s0.sp - 608#64) 296 ∗
            memRegion (s0.sp - 608#64 + 296#64) 152 ∗
            preKeyCalleeSavedAt (s0.sp - 608#64) s0)
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  rcases herr with hnil | ⟨vb, body, hcons, hcase⟩
  · have hx1_0 : s0.readReg64 .x1 = 0#64 := by rw [hx1, hnil]; rfl
    have hparse : Pksm.pksmParse x.bytes = none := by rw [hnil]; exact pksmParse_nil
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ memRegion (sp' + 512#64) 96) ∗
        (memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (prologue_nil_to_504_placed_wpE (A := A) hnil hpc hrun hsp hcl hx1_0 hx8) ?_
    intro sf Pf ⟨hstf, hentf⟩
    refine ⟨hstf, hparse, .ciphertextMessageTooShort 0,
      Entails.trans (sepConj_mono_left hentf) ?_⟩
    apply entails_of_eq; ac_rfl
  · have hne : x.bytes ≠ [] := by rw [hcons]; simp
    refine SepWPp.mono_pre
      (P' := memRegion (sp' + 512#64) 96 ∗
        ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗
          memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
      (by apply entails_of_eq; ac_rfl) ?_
    refine Wire.SepWPp.bind_frame_tryFrom
      (prologue_entry_ne_nil_placed_wpX hne hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    by_cases hlt3 : (vb >>> 4) < 3#8
    · have hvb30 : vb < 0x30#8 := by
        rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt3
        rw [BitVec.lt_def]; change vb.toNat / 16 < 3 at hlt3; change vb.toNat < 48; omega
      have hparse : Pksm.pksmParse x.bytes = none := by rw [hcons]; exact pksmParse_legacy hvb30
      refine SepWPp.mono_pre
        (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗
          (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
        (by apply entails_of_eq; ac_rfl) ?_
      refine SepWPp.frame_tryFrom
        (prologue_28_legacyVer_placed_wpE (A := A) hcons hlt3 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
      intro sf Pf ⟨hstf, hentf⟩
      refine ⟨hstf, hparse, .legacyCiphertextVersion (vb >>> 4),
        Entails.trans (sepConj_mono_left hentf) ?_⟩
      apply entails_of_eq; ac_rfl
    · by_cases hgt4 : 4#8 < (vb >>> 4)
      · have hvb4f : 0x4f#8 < vb := by
          have hvb_lt := vb.isLt
          rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hgt4
          rw [BitVec.lt_def]; change 4 < vb.toNat / 16 at hgt4; change 79 < vb.toNat; omega
        have hparse : Pksm.pksmParse x.bytes = none := by rw [hcons]; exact pksmParse_unrec hvb4f
        refine SepWPp.mono_pre
          (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗
            (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.frame_tryFrom
          (prologue_28_unrecognizedVer_placed_wpE (A := A) hcons hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
        intro sf Pf ⟨hstf, hentf⟩
        refine ⟨hstf, hparse, .unrecognizedCiphertextVersion (vb >>> 4),
          Entails.trans (sepConj_mono_left hentf) ?_⟩
        apply entails_of_eq; ac_rfl
      · have hbody : body = [] := by
          rcases hcase with h | h | h
          · exact absurd h hlt3
          · exact absurd h hgt4
          · exact h
        have hparse : Pksm.pksmParse x.bytes = none := by
          rw [hcons, hbody]; exact pksmParse_bkNone decodeProto_nil rfl
        have hbytes1 : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) := by
          rw [hcons, hbody, pointsToBytes_singleton]
        refine SepWPp.mono_pre
          (P' := (x.ptr ↦₈ vb) ∗ (preKeyCalleeSavedAt sp' s0 ∗ memRegion x.ret 248 ∗
            memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by rw [← hbytes1]; apply entails_of_eq; ac_rfl) ?_
        refine Wire.SepWPp.bind_frame_tryFrom
          (prologue_28_validVer_placed_wpX hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
        intro s2 P2 hpc2 hrun2 ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
        refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_; clear hent2
        have hx1_2' : s2.readReg64 .x1 = 1#64 := by rw [hx1_2, hcons, hbody]; rfl
        refine SepWPp.mono_pre
          (P' := memRegion (sp' + 296#64) 152 ∗ ((x.ptr ↦ₛ x.bytes) ∗
            preKeyCalleeSavedAt sp' s0 ∗ memRegion x.ret 248 ∗ memRegion sp' 296))
          (by rw [← hbytes1]; apply entails_of_eq; ac_rfl) ?_
        refine Wire.SepWPp.bind_frame_tryFrom
          (prologue_80_init_placed_wpX hst2 hpc2 hrun2 hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
        intro s3 P3 hpc3 hrun3 ⟨hst3, hpstate3, hx29_3, hx27_3, _, _, _, hx19_3, _, _, hent3⟩
        refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_; clear hent3
        refine SepWPp.mono_pre
          (P' := (memRegion x.ret 248 ∗ memRegion sp' 296 ∗
            ((sp' + 296#64) ↦₆₄ (x.ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
            (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
              ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
              ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
              ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
              ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
              ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
              ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
              ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64))) ∗ ((x.ptr ↦ₛ x.bytes) ∗ preKeyCalleeSavedAt sp' s0))
          (by simp only [BitVec.sub_self]; apply entails_of_eq; ac_rfl) ?_
        refine SepWPp.frame_tryFrom
          (prologue_bc_len1_to_504_placed_wpE (A := A) (ptr := x.ptr)
            hst3 hpc3 hrun3 hpstate3 hx29_3 hx27_3 hx19_3) ?_
        intro sf Pf ⟨hstf, hentf⟩
        refine ⟨hstf, hparse, .invalidProtobufEncoding,
          Entails.trans (sepConj_mono_left hentf) ?_⟩
        apply entails_of_eq; ac_rfl

theorem preKey_valid_to_460_placed_wpW [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced A H)
    {x : RunCompose.PksmGhost} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {s0 : State}
    (hcons : x.bytes = vb :: b1 :: bs1)
    (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1120#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 ∗
        A.pool ∗ stackAt (s0.sp - 608#64) (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
          (BitVec.ofNat 64 x.bytes.length) x.ptr vb sf ∧
        (Pf ⊢ (x.ptr ↦₈ vb) ∗
          preKeyLoopExitMem A (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1)
            (sf.readReg64 .x24) (Pksm.decodeProto (b1 :: bs1)) ∗
          preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      (tryFromQp s0) := by
  set sp' := s0.sp - 608#64
  have hne : x.bytes ≠ [] := by rw [hcons]; simp
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 512#64) 96 ∗ ((x.ptr ↦ₛ x.bytes) ∗
      memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (prologue_entry_ne_nil_placed_wpX hne hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) := by
    rw [hcons, pointsToBytes_cons]
  refine SepWPp.mono_pre
    (P' := (x.ptr ↦₈ vb) ∗ (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
      preKeyCalleeSavedAt sp' s0 ∗
      memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
      A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by rw [hbytes]; apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.bind_frame_tryFrom
    (prologue_28_validVer_placed_wpX hge3 hle4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_; clear hent2
  refine SepWPp.mono_pre
    (P' := (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100)) ∗
      ((x.ptr ↦₈ vb) ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; ac_rfl) ?_
  have hlt' : (vb :: b1 :: bs1).length < 2 ^ 32 := by rwa [← hcons]
  have hx1_2' : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length := by rwa [← hcons]
  refine SepWPp.frame_tryFrom
    (preKey_init_to_460_placed_wpW hLoopF4 hlt' hst2 hpc2 hrun2
      hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
  intro sf Pf ⟨hstf, hentf⟩
  rw [← hcons] at hstf
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  apply entails_of_eq; ac_rfl

/-! ## 4. `mergePreKeyField_placed_cps`, `preKeyStep_placed_wp` & `preKeyDecodeLoop_e4_placed` -/

theorem mergePreKeyField_placed_cps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.skipFieldSpecX A)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hpc : s.pc = (blkPl_111).base + 0x170#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (m' : ProtoPreKeySignalMessage) (rest : List (BitVec 8)) (s1 : State),
      Pksm.mergeProtoField m tag wt bs = some (m', rest) →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m')
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0))
    (hnone : Pksm.mergeProtoField m tag wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs res) (tryFromQp s0) := by
  refine dispatchPK_placed_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hcl htr
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hsp1 hcl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx0_1 hx1_1 hsp1 hcl1 htr1 => ?_)
  · subst htag
    exact mergePreKeyId_placed_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with preKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeBaseKey_placed_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with baseKey := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeIdentityKey_placed_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with identityKey := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeMessage_placed_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with message := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeRegId_placed_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with registrationId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeSignedPreKeyId_placed_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with signedPreKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeKyberPreKeyId_placed_cpsX hPush hint32 hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with kyberPreKeyId := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · subst htag
    exact mergeKyberCiphertext_placed_cpsPK hPush hbytes hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with kyberCiphertext := some v } rest s2 (by simp [Pksm.mergeProtoField, hm]))
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_placed_cpsPK hskip hpc1 hrun1 hregs1 (hx0_1.trans hx0) hx1_1 htag_lt
      hsp1 hcl1 htr1 hlen
      (fun rest s2 hs => hcont m rest s2 (by simp [Pksm.mergeProtoField, recursionLimit, hs]))
      (fun hs => hnone (by simp [Pksm.mergeProtoField, recursionLimit, hs]))

theorem preKeyStep_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorFromSpecWithStack A (2 * extHookStack))))
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.decodeVarintSliceSpecX A)))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.skipFieldSpecX A)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {fuel : Nat} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      s.pc = (blkPl_111).base + 0x0e4#64 →
      s.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 32 →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (tryFromQp s0))
    (hpc : s.pc = (blkPl_111).base + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen : (b0 :: bs1).length < 2 ^ 32) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
        wirePreKeyOf A (sp' + 312#64) m)
      (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (tryFromQp s0) := by
  refine decodeKeyPK_placed_cpsX hFrom hSlow hvarint hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [Pksm.decodeProtoLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := Wire.decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by rw [hrest1_eq, List.length_drop]
  have hlen1 : rest1.length < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega) hlen
  refine SepWPp.advance_cursorPK_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine mergePreKeyField_placed_cps hPush hint32 hskip hbytes hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt
    hsp1 hcl1 htr1 hlen1
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => ?_)
    (fun hmf_none => by simp [Pksm.decodeProtoLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := mergePreKeyField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by rw [hrest2_eq, List.length_drop]
  refine SepWPp.advance_cursorPK_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1) = Pksm.decodeProtoLoop fuel m' rest2 := by
    simp [Pksm.decodeProtoLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hpc2 hrun2 hregs2 hsp2 hcl2 htr2 (by omega) (Nat.lt_of_le_of_lt (by omega) hlen1)

theorem preKeyDecodeLoop_e4_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorFromSpecWithStack A (2 * extHookStack))))
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushExternSpecWithStack A (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.decodeVarintSliceSpecX A)))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.int32MergeSpecX A)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.skipFieldSpecX A)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (Prost.bytesMergeRawSpecX A)))
    {s0 : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} :
    ∀ (fuel : Nat) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      s.pc = (blkPl_111).base + 0x0e4#64 →
      s.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 32 →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool ∗ stackAt sp' (Prost.skipFieldStackX 100) ∗
          wirePreKeyOf A (sp' + 312#64) m)
        (preKeyLoopExitPostPlaced A s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcl, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_placed_wpX hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_placed_wpX hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 =>
      refine loopCheckPK_e4_cons_placed_cpsX hpc hrun hregs hsp hcl htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hcl1 htr1
      exact preKeyStep_placed_wp hFrom hPush hSlow hvarint hint32 hskip hbytes
        (preKeyDecodeLoop_e4_placed hFrom hPush hSlow hvarint hint32 hskip hbytes fuel)
        hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hcl1 htr1 hfuel hlen

theorem preKeyDecodeLoopF4W_of_callees_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced A H) :
    PreKeyDecodeLoopF4OkWPlaced A H :=
  fun _ _ _ _ _ _ fuel _ _ _ _ _ hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hfuel hlen =>
    preKeyStep_placed_wp hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
      hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge
      (preKeyDecodeLoop_e4_placed hC.decodeErrorFrom hC.decodeErrorPush hC.decodeVarintSlow
        hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge fuel)
      hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hfuel hlen

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
