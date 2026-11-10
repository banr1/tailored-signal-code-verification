/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32ArmsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlacedBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ParseLemmas
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Unified Prologue and Decode Loop

Allocation-budget (`RustCliAllocBudget M`) proofs of the unified prologue theorems and
capacity-bounded protobuf decode loop (`SigTryFromLoopBoundedEnv`) on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlacedBudget

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet SepProp
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr hiding optU32At
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding
  decodeErrorFromSpecWithStack decodeErrorPushExternSpecWithStack decodeVarintSlowSpecWithStack
open CryptoVerification.LibsignalTripleRatchet.Prost hiding
  decodeVarintSliceSpecX int32MergeSpecX skipFieldSpecX bytesMergeRawSpecX
open CryptoVerification.LibsignalTripleRatchet.Getters hiding lsRustDeallocSym
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack PreKeyLoopRegs PreKeyLoopRegs.of_calleeSaved SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  SepWPp SepWPp.pure_pre SepWPp.exists_pre SepWPp.mono_pre PksmCalleesPlaced
  prologue_bc_len1_to_504_placed_wpE prologue_bc_gt1_to_f4_placed_wpX
  mergeBaseKey_placed_cpsPK mergeIdentityKey_placed_cpsPK
  mergeKyberCiphertext_placed_cpsPK mergeMessage_placed_cpsPK
  mergeKyberPreKeyId_placed_cpsX mergePreKeyId_placed_cpsX
  mergeRegId_placed_cpsX mergeSignedPreKeyId_placed_cpsX
  mergeSkipField_placed_cpsPK
  mergePreKeyField_placed_cps preKeyStep_placed_wp preKeyDecodeLoop_e4_placed
  PreKeyDecodeLoopF4OkWPlaced preKeyDecodeLoopF4W_of_callees_placed_ok
  preKey_init_to_460_placed_wpW preKey_earlyErr_to_504_placed_wpE
  preKey_valid_to_460_placed_wpW
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.BytesArmsPlacedBudget
  (mergeBaseKey_placed_cpsPK mergeIdentityKey_placed_cpsPK
   mergeKyberCiphertext_placed_cpsPK mergeMessage_placed_cpsPK)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
  (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
  (decodeKeyPK_placed_cpsX loopCheckPK_e4_empty_placed_wpX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.E4PortHelpers
  (advance_cursorPK_placed preKeyLoopExitPostPlaced preKeyLoopExitPostPlaced_mono_rem
   preKeyLoopExitPostPlaced_zero_eq sepWP_done_sync_pool_111 sepWP_seg_111
   wirePreKeyLoopCapsOf wirePreKeyOf_empty_entails_loopCapsOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Int32ArmsPlacedBudget
  (mergeKyberPreKeyId_placed_cpsX mergePreKeyId_placed_cpsX
   mergeRegId_placed_cpsX mergeSignedPreKeyId_placed_cpsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.PrologueBPlacedBudget
  (prologue_524_len1_to_504_placed_wpE prologue_bc_len1_to_524_placed_wpX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ProloguePlacedBudget
  (prologue_28_legacyVer_placed_wpE prologue_28_unrecognizedVer_placed_wpE
   prologue_28_validVer_placed_wpX prologue_80_init_placed_wpX
   prologue_entry_ne_nil_placed_wpX prologue_nil_to_504_placed_wpE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SkipArmPlacedBudget
  (mergeSkipField_placed_cpsPK)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromSpecWithStack decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (decodeVarintSliceSpecX int32MergeSpecX skipFieldSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget
  (bmNextCap bytesMergeExactRawSpecX decodeErrorPushBoundedSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget
  (SigTryFromCaps SigTryFromLoopBoundedEnv TryFromLoopEnv fitsEnv_sigLoop_mono_rem
   noPanicQp sepWPp_end_noPanic_placed sepWPp_frame_noPanic sepWPp_mono_post)

private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk

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

theorem sepWPp_anyQp_of_noPanic {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (noPanicQp s)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hqp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact False.elim hqp
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

private theorem sepWPp_perm {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P' Q Qp) (hP : P ⊢ P') :
    SepWPp prog ret s P Q Qp :=
  Wire.SepWPp.mono_pre hP h

private theorem sepWPp_bind_frame_noPanic {prog : Program} {mid ret : BitVec 64}
    {s s0 : State} {P R : SepProp} {Q1 Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P Q1 (noPanicQp s0))
    (h2 : ∀ s1 P1, s1.pc = mid → s1.status = .Running → Q1 s1 P1 →
      SepWPp prog ret s1 (P1 ∗ R) Q (noPanicQp s0)) :
    SepWPp prog ret s (P ∗ R) Q (noPanicQp s0) :=
  Wire.SepWPp.bind (Qm := fun s1 P1' => ∃ P1, Q1 s1 P1 ∧ (P1' ⊢ P1 ∗ R))
    (sepWPp_frame_noPanic h1 fun _ P1 hq1 => ⟨P1, hq1, Entails.refl _⟩)
    fun s1 _ hpc1 hrun1 ⟨P1, hq1, hent⟩ =>
      Wire.SepWPp.mono_pre hent (h2 s1 P1 hpc1 hrun1 hq1)

/-- Converts `withPreKeyInv (LibsignalCodeRoLoaded lsmpl)` subroutine specs to
`withLsCodeRoLoaded lsmpl`. -/
theorem subroutine_ok_cro_of_preKeyInv [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun x _ s0 hp => by
      dsimp only [withLsCodeRoLoaded, withPreKeyInv] at hp ⊢
      exact hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCodeRoLoaded, withPreKeyInv] at hq ⊢
      exact hq)

/-! ## 1. Pure Frame Splitting/Packing Helpers for `prologue_bc_len1_to_504_placed_wpE` -/

private theorem lswb_memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 ⊢
      ∃∗ s104 : BitVec 64, ∃∗ s96 : BitVec 64,
        memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
        memRegion (sp' + 112#64) 184 := by
  rw [show (296 : Nat) = 96 + (16 + 184) by decide,
    CryptoVerification.LibsignalTripleRatchet.Prost.memRegion_split sp' 96 200 (by decide),
    CryptoVerification.LibsignalTripleRatchet.Prost.memRegion_split (sp' + 96#64) 16 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 96#64)))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem lswb_memRegion296_pack (sp' s96 s104 : BitVec 64) :
    memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ ((sp' + 104#64) ↦₆₄ s104) ∗
    memRegion (sp' + 112#64) 184 ⊢
      memRegion sp' 296 := by
  rw [show (296 : Nat) = 96 + (8 + (8 + 184)) by decide,
    CryptoVerification.LibsignalTripleRatchet.Prost.memRegion_split sp' 96 200 (by decide),
    CryptoVerification.LibsignalTripleRatchet.Prost.memRegion_split (sp' + 96#64) 8 192 (by decide),
    CryptoVerification.LibsignalTripleRatchet.Prost.memRegion_split (sp' + 96#64 + 8#64) 8 184 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono_right
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

private theorem lswb_initCells_to_full (sp' : BitVec 64) :
    ((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
    ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
    ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
    ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
    ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
    ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
    ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
    ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4 ⊢
      ∃∗ u436 : BitVec 32, ∃∗ u428 : BitVec 32, ∃∗ u420 : BitVec 32, ∃∗ u412 : BitVec 32,
      ∃∗ msgLen : BitVec 64, ∃∗ msgPtr : BitVec 64, ∃∗ ikLen : BitVec 64, ∃∗ ikPtr : BitVec 64,
      ∃∗ bkLen : BitVec 64, ∃∗ bkPtr : BitVec 64, ∃∗ kyberLen : BitVec 64, ∃∗ kyberPtr : BitVec 64,
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗
        ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗
        ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) := by
  have hm4 (a : BitVec 64) : memRegion a 4 = (∃∗ u : BitVec 32, a ↦₃₂ u) := ProofLib.memRegion_four a
  rw [hm4 (sp' + 412#64), hm4 (sp' + 420#64), hm4 (sp' + 428#64), hm4 (sp' + 436#64)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 320#64))
      (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 344#64))
        (sepConj_mono_right (sepConj_mono (memRegion16_split8_8' (sp' + 368#64))
          (sepConj_mono_right (sepConj_mono_left (memRegion16_split8_8' (sp' + 392#64)))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.refl _

private theorem lswb_full_cells_memRegion128 (sp' : BitVec 64)
    (w312 kyberPtr kyberLen w336 bkPtr bkLen w360 ikPtr ikLen w384 msgPtr msgLen : BitVec 64)
    (u408 u412 u416 u420 u424 u428 u432 u436 : BitVec 32) :
    ((sp' + 312#64) ↦₆₄ w312) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
    ((sp' + 336#64) ↦₆₄ w336) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
    ((sp' + 360#64) ↦₆₄ w360) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
    ((sp' + 384#64) ↦₆₄ w384) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
    ((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗ ((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
    ((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗ ((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436) ⊢
      memRegion (sp' + 312#64) 128 := by
  have hw24 (a w0 w1 w2 : BitVec 64) : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide, Prost.memRegion_split a 8 16 (by decide),
      Prost.memRegion_split (a + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hu8 (a : BitVec 64) (v0 v4 : BitVec 32) : (a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v4) ⊢ memRegion a 8 := by
    rw [show (8 : Nat) = 4 + 4 by decide, Prost.memRegion_split a 4 4 (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _)
  have h312 := hw24 (sp' + 312#64) w312 kyberPtr kyberLen; have h336 := hw24 (sp' + 336#64) w336 bkPtr bkLen
  have h360 := hw24 (sp' + 360#64) w360 ikPtr ikLen; have h384 := hw24 (sp' + 384#64) w384 msgPtr msgLen
  have h408 := hu8 (sp' + 408#64) u408 u412; have h416 := hu8 (sp' + 416#64) u416 u420
  have h424 := hu8 (sp' + 424#64) u424 u428; have h432 := hu8 (sp' + 432#64) u432 u436
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
      (((sp' + 408#64) ↦₃₂ u408) ∗ ((sp' + 412#64) ↦₃₂ u412)) ∗ (((sp' + 416#64) ↦₃₂ u416) ∗ ((sp' + 420#64) ↦₃₂ u420)) ∗
      (((sp' + 424#64) ↦₃₂ u424) ∗ ((sp' + 428#64) ↦₃₂ u428)) ∗ (((sp' + 432#64) ↦₃₂ u432) ∗ ((sp' + 436#64) ↦₃₂ u436)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact sepConj_mono h312 (sepConj_mono h336 (sepConj_mono h360 (sepConj_mono h384
    (sepConj_mono h408 (sepConj_mono h416 (sepConj_mono h424 h432))))))

private theorem lswb_region152_repack (sp' c0 c1 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ c0) ∗ ((sp' + 304#64) ↦₆₄ c1) ∗ memRegion (sp' + 312#64) 128 ∗ ((sp' + 440#64) ↦₆₄ w440) ⊢
      memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (128 + 8)) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 128 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (Entails.refl _) (pointsTo64_entails_memRegion _ _)))

/-! ## 2. `prologue_bc_len1_to_504_placed_wpE` and `prologue_bc_gt1_to_f4_placed_wpX` -/

theorem prologue_bc_len1_to_504_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    {sret sp' ptr : BitVec 64} {s0 s3 : State} {Qp : State → SepProp → Prop}
    (hst : PostEpilogueStatePlaced s0 sp' s3) (hpc : s3.pc = (blkPl_111).base + 188#64)
    (hrun : s3.status = .Running) (hpstate : s3.pstate = subsPState64 1#64 1#64)
    (hx29 : s3.readReg64 .x29 = sp' + 512#64) (hx27 : s3.readReg64 .x27 = 0x8000000000000002#64)
    (hx19 : s3.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s3
      (memRegion sret 248 ∗ memRegion sp' 296 ∗ ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
          ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
          ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool lim st s3)
      (fun sf Pf => PostEpilogueStatePlaced s0 sp' sf ∧
        (Pf ⊢ pksmErrE A.repAlloc [] sret .invalidProtobufEncoding ∗
          memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152 ∗ A.pool lim st sf))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono (lswb_memRegion296_split sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (lswb_initCells_to_full sp')))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun u436 => Wire.SepWPp.exists_pre fun u428 =>
    Wire.SepWPp.exists_pre fun u420 => Wire.SepWPp.exists_pre fun u412 =>
    Wire.SepWPp.exists_pre fun msgLen => Wire.SepWPp.exists_pre fun msgPtr =>
    Wire.SepWPp.exists_pre fun ikLen => Wire.SepWPp.exists_pre fun ikPtr =>
    Wire.SepWPp.exists_pre fun bkLen => Wire.SepWPp.exists_pre fun bkPtr =>
    Wire.SepWPp.exists_pre fun kyberLen => Wire.SepWPp.exists_pre fun kyberPtr =>
    Wire.SepWPp.exists_pre fun s104 => Wire.SepWPp.exists_pre fun s96 => ?_
  refine Wire.SepWPp.mono_pre
    (P' := ((((sp' + 104#64) ↦₆₄ s104) ∗ ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr)) ∗ A.pool lim st s3) ∗
      (memRegion sret 248 ∗ memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 328#64) ↦₆₄ kyberLen) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗ ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗ ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (prologue_bc_len1_to_524_placed_wpX (A := A) (lim := lim) (st := st) hst hpc hrun hpstate hx29 hx27 hx19) ?_
  intro s4 P4 hpc4 hrun4 ⟨⟨hst4, hx29_4, hx28_4, hx27_4, hx26_4, hx23_4, hx19_4, _, hx1_4⟩, hent4⟩
  refine Wire.SepWPp.mono_pre (sepConj_mono_left hent4) ?_; clear hent4
  refine Wire.SepWPp.mono_pre
    (P' := ((memRegion sret 248 ∗ ((sp' + 96#64) ↦₆₄ s96) ∗
        ((sp' + 312#64) ↦₆₄ noneCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
        ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
        ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
        ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
        ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗ ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
        ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗ ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
        A.pool lim st s4) ∗
      (memRegion sp' 96 ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184 ∗
        ((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_frame_noPanic
    (prologue_524_len1_to_504_placed_wpE (A := A) (lim := lim) (st := st)
      hst4 hpc4 hrun4 hx29_4 hx28_4 hx27_4 hx26_4 hx23_4 hx19_4 hx1_4) ?_
  intro sf Pf ⟨hstf, hentf⟩
  refine ⟨hstf, Entails.trans (sepConj_mono_left hentf) ?_⟩
  have hm296 := lswb_memRegion296_pack sp' (s4.readReg64 .x8) ikPtr
  have hm128 := lswb_full_cells_memRegion128 sp'
    0x8000000000000002#64 kyberPtr kyberLen noneCap bkPtr bkLen noneCap ikPtr ikLen noneCap msgPtr msgLen
    0#32 u412 0#32 u420 0#32 u428 0#32 u436
  have hm152 := lswb_region152_repack sp' (ptr + 1#64) 0#64 (sp' + 296#64)
  refine Entails.trans (Q := pksmErrE A.repAlloc [] sret .invalidProtobufEncoding ∗
      (memRegion sp' 96 ∗ ((sp' + 96#64) ↦₆₄ (s4.readReg64 .x8)) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 112#64) 184) ∗
      (((sp' + 296#64) ↦₆₄ (ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        (((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗ ((sp' + 328#64) ↦₆₄ kyberLen) ∗
          ((sp' + 336#64) ↦₆₄ noneCap) ∗ ((sp' + 344#64) ↦₆₄ bkPtr) ∗ ((sp' + 352#64) ↦₆₄ bkLen) ∗
          ((sp' + 360#64) ↦₆₄ noneCap) ∗ ((sp' + 368#64) ↦₆₄ ikPtr) ∗ ((sp' + 376#64) ↦₆₄ ikLen) ∗
          ((sp' + 384#64) ↦₆₄ noneCap) ∗ ((sp' + 392#64) ↦₆₄ msgPtr) ∗ ((sp' + 400#64) ↦₆₄ msgLen) ∗
          ((sp' + 408#64) ↦₃₂ 0#32) ∗ ((sp' + 412#64) ↦₃₂ u412) ∗ ((sp' + 416#64) ↦₃₂ 0#32) ∗ ((sp' + 420#64) ↦₃₂ u420) ∗
          ((sp' + 424#64) ↦₃₂ 0#32) ∗ ((sp' + 428#64) ↦₃₂ u428) ∗ ((sp' + 432#64) ↦₃₂ 0#32) ∗ ((sp' + 436#64) ↦₃₂ u436)) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))) ∗ A.pool lim st sf)
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepConj_mono_right (sepConj_mono hm296 (sepConj_mono_left ?_))
  exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hm128)))
    (by simpa [sepConj_assoc] using hm152)

theorem prologue_bc_gt1_to_f4_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {sret sp' ptr : BitVec 64} {vb : BitVec 8} {n : Nat}
    {s0 s3 : State} {Qp : State → SepProp → Prop}
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
      (A.pool lim st s3)
      (fun s4 P4 =>
        (PreKeyLoopRegs sp' sret (BitVec.ofNat 64 n) ptr vb s4 ∧
        PostEpilogueStatePlaced s0 sp' s4 ∧
        s4.readReg64 .x28 = sp' + 296#64 ∧
        s4.readReg64 .x26 = sp' + 304#64 ∧
        s4.readReg64 .x2 = BitVec.ofNat 64 n - 1#64) ∧
        (P4 ⊢ A.pool lim st s4))
      Qp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcond_eq := cond_eq_subs1_false_w40 hge2 hlt
  refine sepWPp_anyQp_of_noPanic (sepWPp_end_noPanic_placed (s0 := s0) hcl ?_)
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st (F := emp) fun _ hcl4 => ?_
  refine ⟨⟨⟨by simp [hsp_eq, arm64_norm], by simp [hx29, arm64_norm],
    by simp [hx27, arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩,
    ⟨by simp [hsp_eq, arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp,
      hcl4, by simp [htr, arm64_norm]⟩,
    by simp [arm64_norm], by simp [arm64_norm], by simp [hx2, arm64_norm]⟩,
    by rw [sepConj_emp]; exact Entails.refl _⟩

/-! ## 3. Pool-Syncing Loop-Head & Tag-Dispatch Combinators (`+0x0e4`, `+0x170`) -/

set_option maxHeartbeats 800000 in
theorem loopCheckPK_e4_cons_placed_cpsX_pool [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x0e4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 32)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_111).base + 0x0f4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x28 = sp' + 296#64 → s1.readReg64 .x26 = sp' + 304#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          A.pool lim st s1 ∗ F)
        Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        A.pool lim st s ∗ F)
      Q Qp := by
  change s.pc = (blkPl_111).base + 228#64 at hpc
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 512#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 (by omega)
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 244#64) ?_
  apply sepWP_seg_111; intro _m_strip
  wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine Wire.SepWPp.mono_pre ?_
    (hcont _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [arm64_norm] using hregs.x27, by simpa [arm64_norm] using hregs.x25,
       by simpa [arm64_norm] using hregs.x23, by simpa [arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x21, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19⟩
      (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1 htr)
  unfold sliceCursorAt; apply entails_of_eq; sep_ac_rfl

set_option maxHeartbeats 1200000 in
theorem dispatchPK_placed_cps_pool [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8}
    {tag : Nat} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_111).base + 0x170#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x260#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h2 : tag = 2 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x190#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h3 : tag = 3 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x2a0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h4 : tag = 4 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x200#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h5 : tag = 5 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x280#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h6 : tag = 6 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x1d0#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h7 : tag = 7 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x2c8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h8 : tag = 8 → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x238#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp)
    (h9 : 9 ≤ tag → ∀ s1 : State, s1.pc = (blkPl_111).base + 0x2d8#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.readReg64 .x0 = s.readReg64 .x0 → s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1 (A.pool lim st s1 ∗ F) Q Qp) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s (A.pool lim st s ∗ F) Q Qp := by
  change s.pc = (blkPl_111).base + 368#64 at hpc
  let mkRegs (s1 : State)
      (hsp' : s1.sp = s.sp) (h29 : s1.readReg64 .x29 = s.readReg64 .x29)
      (h27 : s1.readReg64 .x27 = s.readReg64 .x27) (h25 : s1.readReg64 .x25 = s.readReg64 .x25)
      (h23 : s1.readReg64 .x23 = s.readReg64 .x23) (h22 : s1.readReg64 .x22 = s.readReg64 .x22)
      (h21 : s1.readReg64 .x21 = s.readReg64 .x21) (h20 : s1.readReg64 .x20 = s.readReg64 .x20)
      (h19 : s1.readReg64 .x19 = s.readReg64 .x19) : PreKeyLoopRegs sp' sret len ptr0 vb s1 :=
    ⟨hsp'.trans hregs.sp, h29.trans hregs.x29, h27.trans hregs.x27, h25.trans hregs.x25,
     h23.trans hregs.x23, h22.trans hregs.x22, h21.trans hregs.x21, h20.trans hregs.x20,
     h19.trans hregs.x19⟩
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 608#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h1 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 400#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h2 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 672#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h3 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 4#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 512#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h4 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 5#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 640#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h5 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 6#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 464#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h6 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 7#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 712#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h7 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 8#64 := hx1
    refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 568#64) ?_
    apply sepWP_seg_111; intro _m_strip; wp_steps
    refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h8 rfl _ (by simp [arm64_norm])
      (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
      (by simp [arm64_norm]) (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 9) := hx1
    obtain ⟨hc1, hc2, hc2_ne, hc3, hc3_ne, hc4, hc4_ne, hc5, hc6, hc6_ne, hc7, hc7_ne, hc8, hc8_ne⟩ :=
      tag_ge9_conds (n + 9) (by omega) htag_lt
    cases hgt4 : BitVec.slt 4#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32) <;>
    [ cases hgt2 : BitVec.slt 2#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32);
      cases hgt6 : BitVec.slt 6#32 ((BitVec.ofNat 64 (n + 9)).setWidth 32) ] <;>
    { refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 728#64) ?_
      apply sepWP_seg_111; intro _m_strip; wp_steps
      refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => h9 (by omega) _ (by simp [arm64_norm])
        (by simp [hrun, arm64_norm]) (mkRegs _ (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
        (by simp [arm64_norm]) (by simpa [arm64_norm] using hx1')
        (by simpa [State.spAligned, arm64_norm] using hsp) hcl1 htr }

/-! ## 4. `mergePreKeyField_placed_cps`, `preKeyStep_placed_wp` & `preKeyDecodeLoop_e4_placed` -/

theorem mergePreKeyField_placed_cps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {rem : Nat} {caps : SigTryFromCaps} {H : LibsignalHooks}
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (int32MergeSpecX A lim)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (skipFieldSpecX A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {tag : Nat} {wt : WireType} {bs : List (BitVec 8)}
    {m : ProtoPreKeySignalMessage} {res : Option ProtoPreKeySignalMessage}
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv rem caps))
    (hmax : bs.length ≤ rem)
    (hpc : s.pc = (blkPl_111).base + 0x170#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace) (hlen : bs.length < 2 ^ 32)
    (hcont : ∀ (m' : ProtoPreKeySignalMessage) (rest : List (BitVec 8))
      (caps' : SigTryFromCaps) (evs₁ : List AllocEvent) (s1 : State),
      Pksm.mergeProtoField m tag wt bs = some (m', rest) →
      FitsEnv M lim (M.stepEvents evs₁ st) (SigTryFromLoopBoundedEnv rest.length caps') →
      s1.pc = (blkPl_111).base + 0x0e4#64 →
      s1.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s1
        (sliceCursorAfter (sp' + 296#64) ptr bs rest ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim (M.stepEvents evs₁ st) s1 ∗
          stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps' m')
        (preKeyLoopExitPostPlaced A lim (M.stepEvents evs₁ st) rest.length caps'
          s0 sp' sret len ptr0 vb ptr bs res)
        (noPanicQp s0))
    (hnone : Pksm.mergeProtoField m tag wt bs = none → res = none) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st rem caps s0 sp' sret len ptr0 vb ptr bs res)
      (noPanicQp s0) := by
  have hPush_c := subroutine_ok_cro_of_preKeyInv hPush
  have hint32_c := subroutine_ok_cro_of_preKeyInv hint32
  have hskip_c := subroutine_ok_cro_of_preKeyInv hskip
  have hbytes_c := subroutine_ok_cro_of_preKeyInv hbytes
  refine Wire.SepWPp.mono_pre
    (P' := A.pool lim st s ∗
      (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine dispatchPK_placed_cps_pool (A := A) (lim := lim) (st := st)
    hpc hrun hregs hx1 htag_ge htag_lt hsp hcl htr
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
    refine sepWPp_perm (mergePreKeyId_placed_cpsX hPush_c hint32_c hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
        have hmf : Pksm.mergeProtoField m 1 wt bs = some ({ m with preKeyId := some v }, rest) := by
          simp [Pksm.mergeProtoField, hm]
        obtain ⟨k, _hk_le, rfl⟩ := mergePreKeyField_suffix hmf
        have hrem : (bs.drop k).length ≤ rem := by simp; omega
        refine sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hrem) ?_
        simpa [M.stepEvents_nil] using hcont { m with preKeyId := some v } (bs.drop k) caps [] s2
          hmf (by simpa [M.stepEvents_nil] using fitsEnv_sigLoop_mono_rem hrem hfit)
          hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeBaseKey_placed_cpsPK hPush_c hbytes_c hfit hmax hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest evs₁ s2 hm _hcap_lt _hevs₁ hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2 =>
        hcont { m with baseKey := some v } rest
          (caps.set .ct (bmNextCap (caps.get .ct) v.length)) evs₁ s2
          (by simp [Pksm.mergeProtoField, hm]) hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeIdentityKey_placed_cpsPK hPush_c hbytes_c hfit hmax hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest evs₁ s2 hm _hcap_lt _hevs₁ hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2 =>
        hcont { m with identityKey := some v } rest
          (caps.set .pq (bmNextCap (caps.get .pq) v.length)) evs₁ s2
          (by simp [Pksm.mergeProtoField, hm]) hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeMessage_placed_cpsPK hPush_c hbytes_c hfit hmax hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest evs₁ s2 hm _hcap_lt _hevs₁ hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2 =>
        hcont { m with message := some v } rest
          (caps.set .ad (bmNextCap (caps.get .ad) v.length)) evs₁ s2
          (by simp [Pksm.mergeProtoField, hm]) hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeRegId_placed_cpsX hPush_c hint32_c hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
        have hmf : Pksm.mergeProtoField m 5 wt bs = some ({ m with registrationId := some v }, rest) := by
          simp [Pksm.mergeProtoField, hm]
        obtain ⟨k, _hk_le, rfl⟩ := mergePreKeyField_suffix hmf
        have hrem : (bs.drop k).length ≤ rem := by simp; omega
        refine sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hrem) ?_
        simpa [M.stepEvents_nil] using hcont { m with registrationId := some v } (bs.drop k) caps [] s2
          hmf (by simpa [M.stepEvents_nil] using fitsEnv_sigLoop_mono_rem hrem hfit)
          hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeSignedPreKeyId_placed_cpsX hPush_c hint32_c hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
        have hmf : Pksm.mergeProtoField m 6 wt bs = some ({ m with signedPreKeyId := some v }, rest) := by
          simp [Pksm.mergeProtoField, hm]
        obtain ⟨k, _hk_le, rfl⟩ := mergePreKeyField_suffix hmf
        have hrem : (bs.drop k).length ≤ rem := by simp; omega
        refine sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hrem) ?_
        simpa [M.stepEvents_nil] using hcont { m with signedPreKeyId := some v } (bs.drop k) caps [] s2
          hmf (by simpa [M.stepEvents_nil] using fitsEnv_sigLoop_mono_rem hrem hfit)
          hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeKyberPreKeyId_placed_cpsX hPush_c hint32_c hfit hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest s2 hm hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
        have hmf : Pksm.mergeProtoField m 7 wt bs = some ({ m with kyberPreKeyId := some v }, rest) := by
          simp [Pksm.mergeProtoField, hm]
        obtain ⟨k, _hk_le, rfl⟩ := mergePreKeyField_suffix hmf
        have hrem : (bs.drop k).length ≤ rem := by simp; omega
        refine sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hrem) ?_
        simpa [M.stepEvents_nil] using hcont { m with kyberPreKeyId := some v } (bs.drop k) caps [] s2
          hmf (by simpa [M.stepEvents_nil] using fitsEnv_sigLoop_mono_rem hrem hfit)
          hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · subst htag
    refine sepWPp_perm (mergeKyberCiphertext_placed_cpsPK hPush_c hbytes_c hfit hmax hpc1 hrun1 hregs1 (hx0_1.trans hx0) hsp1 hcl1 htr1 hlen
      (fun v rest evs₁ s2 hm _hcap_lt _hevs₁ hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2 =>
        hcont { m with kyberCiphertext := some v } rest
          (caps.set .rk (bmNextCap (caps.get .rk) v.length)) evs₁ s2
          (by simp [Pksm.mergeProtoField, hm]) hfit_tail hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hm => hnone (by simp [Pksm.mergeProtoField, hm])))
      (by apply entails_of_eq; sep_ac_rfl)
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    refine sepWPp_perm (mergeSkipField_placed_cpsPK hskip_c hfit hpc1 hrun1 hregs1
      (hx0_1.trans hx0) hx1_1 htag_lt hsp1 hcl1 htr1 hlen
      (fun rest s2 hs hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => by
        have hmf : Pksm.mergeProtoField m (n + 9) wt bs = some (m, rest) := by
          simp [Pksm.mergeProtoField, recursionLimit, hs]
        obtain ⟨k, _hk_le, rfl⟩ := mergePreKeyField_suffix hmf
        have hrem : (bs.drop k).length ≤ rem := by simp; omega
        refine sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hrem) ?_
        simpa [M.stepEvents_nil] using hcont m (bs.drop k) caps [] s2
          hmf (by simpa [M.stepEvents_nil] using fitsEnv_sigLoop_mono_rem hrem hfit)
          hpc2 hrun2 hregs2 hsp2 hcl2 htr2)
      (fun hs => hnone (by simp [Pksm.mergeProtoField, recursionLimit, hs])))
      (by apply entails_of_eq; sep_ac_rfl)

theorem preKeyStep_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {caps : SigTryFromCaps} {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeVarintSliceSpecX A lim)))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (int32MergeSpecX A lim)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (skipFieldSpecX A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (bytesMergeExactRawSpecX A lim)))
    {s0 s : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} {ptr : BitVec 64}
    {fuel : Nat} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    (ih : ∀ {st' : M.σ} {caps' : SigTryFromCaps} {s : State} {ptr : BitVec 64}
      {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      FitsEnv M lim st' (SigTryFromLoopBoundedEnv bs.length caps') →
      s.pc = (blkPl_111).base + 0x0e4#64 →
      s.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 32 →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st' s ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps' m)
        (preKeyLoopExitPostPlaced A lim st' bs.length caps'
          s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (noPanicQp s0))
    (hfit : FitsEnv M lim st (SigTryFromLoopBoundedEnv (b0 :: bs1).length caps))
    (hpc : s.pc = (blkPl_111).base + 0x0f4#64)
    (hrun : s.status = .Running) (hregs : PreKeyLoopRegs sp' sret len ptr0 vb s)
    (hx28 : s.readReg64 .x28 = sp' + 296#64) (hx26 : s.readReg64 .x26 = sp' + 304#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen : (b0 :: bs1).length < 2 ^ 32) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st (b0 :: bs1).length caps
        s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      (noPanicQp s0) := by
  refine decodeKeyPK_placed_cpsX
    (subroutine_ok_cro_of_preKeyInv hFrom)
    (subroutine_ok_cro_of_preKeyInv hSlow)
    (subroutine_ok_cro_of_preKeyInv hvarint)
    hfit hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcl1 htr1 hx0_1 hx1_1 => ?_)
    (fun hdk_none => by simp [Pksm.decodeProtoLoop, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := Wire.decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by rw [hrest1_eq, List.length_drop]
  have hlen1 : rest1.length < 2 ^ 32 := Nat.lt_of_le_of_lt (by omega) hlen
  have hmax1 : rest1.length ≤ (b0 :: bs1).length := by omega
  refine advance_cursorPK_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine mergePreKeyField_placed_cps
    hPush hint32 hskip hbytes hfit hmax1
    hpc1 hrun1 hregs1 hx0_1 hx1_1 htag_ge htag_lt hsp1 hcl1 htr1 hlen1
    (fun m' rest2 caps' evs₁ s2 hmf hfit_next hpc2 hrun2 hregs2 hsp2 hcl2 htr2 => ?_)
    (fun hmf_none => by simp [Pksm.decodeProtoLoop, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := mergePreKeyField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by rw [hrest2_eq, List.length_drop]
  refine advance_cursorPK_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1) =
      Pksm.decodeProtoLoop fuel m' rest2 := by
    simp [Pksm.decodeProtoLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hfit_next hpc2 hrun2 hregs2 hsp2 hcl2 htr2
    (by omega) (Nat.lt_of_le_of_lt (by omega) hlen1)

theorem preKeyDecodeLoop_e4_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeVarintSliceSpecX A lim)))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (int32MergeSpecX A lim)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (skipFieldSpecX A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (bytesMergeExactRawSpecX A lim)))
    {s0 : State} {sp' sret len ptr0 : BitVec 64} {vb : BitVec 8} :
    ∀ (fuel : Nat) {st : M.σ} {caps : SigTryFromCaps} {s : State} {ptr : BitVec 64}
      {bs : List (BitVec 8)} {m : ProtoPreKeySignalMessage},
      FitsEnv M lim st (SigTryFromLoopBoundedEnv bs.length caps) →
      s.pc = (blkPl_111).base + 0x0e4#64 →
      s.status = .Running → PreKeyLoopRegs sp' sret len ptr0 vb s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 32 →
      SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
        (sliceCursorAt (sp' + 296#64) ptr bs ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
          wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
        (preKeyLoopExitPostPlaced A lim st bs.length caps
          s0 sp' sret len ptr0 vb ptr bs (Pksm.decodeProtoLoop fuel m bs))
        (noPanicQp s0)
  | 0, _st, _caps, s, _ptr, bs, _m, _hfit, hpc, hrun, hregs, hsp, hcl, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_placed_wpX hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, st, caps, s, ptr, bs, m, hfit, hpc, hrun, hregs, hsp, hcl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopCheckPK_e4_empty_placed_wpX hpc hrun hregs hsp hcl htr rfl
    | cons b0 bs1 =>
      refine Wire.SepWPp.mono_pre
        (P' := sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          A.pool lim st s ∗ (memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100) ∗
            wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine loopCheckPK_e4_cons_placed_cpsX_pool (A := A) (lim := lim) (st := st)
        hpc hrun hregs hsp hcl htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hcl1 htr1
      refine sepWPp_perm (preKeyStep_placed_wp hFrom hPush hSlow hvarint hint32 hskip hbytes
        (preKeyDecodeLoop_e4_placed hFrom hPush hSlow hvarint hint32 hskip hbytes fuel)
        hfit hpc1 hrun1 hregs1 hx28_1 hx26_1 hx2_1 hsp1 hcl1 htr1 hfuel hlen)
        (by apply entails_of_eq; sep_ac_rfl)

/-! ## 5. `PreKeyDecodeLoopF4OkWPlaced` & Unified Prologue Theorems -/

def PreKeyDecodeLoopF4OkWPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (st : M.σ) (maxLen : Nat) (caps : SigTryFromCaps) (s0 : State)
    (sp' sret len ptr0 : BitVec 64) (vb : BitVec 8) (fuel : Nat) (s : State)
    (ptr : BitVec 64) (b0 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) {Qp : State → SepProp → Prop},
    FitsEnv M lim st (SigTryFromLoopBoundedEnv maxLen caps) →
    (b0 :: bs1).length ≤ maxLen →
    s.pc = (blkPl_111).base + 0x0f4#64 →
    s.status = .Running →
    PreKeyLoopRegs sp' sret len ptr0 vb s →
    s.readReg64 .x28 = sp' + 296#64 → s.readReg64 .x26 = sp' + 304#64 →
    s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
    s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
    (b0 :: bs1).length ≤ fuel + 1 → (b0 :: bs1).length < 2 ^ 32 →
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 0x460#64) s
      (sliceCursorAt (sp' + 296#64) ptr (b0 :: bs1) ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s ∗ stackAt sp' (skipFieldStackX 100) ∗
        wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) caps m)
      (preKeyLoopExitPostPlaced A lim st maxLen caps
        s0 sp' sret len ptr0 vb ptr (b0 :: bs1)
        (Pksm.decodeProtoLoop (fuel + 1) m (b0 :: bs1)))
      Qp

theorem preKeyDecodeLoopF4W_of_subroutines_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 261)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))))
    (hPush : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 257)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeErrorPushBoundedSpecWithStack M A lim (2 * extHookStack))))
    (hSlow : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 293)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl)
        (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))))
    (hvarint : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 76)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (decodeVarintSliceSpecX A lim)))
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (int32MergeSpecX A lim)))
    (hskip : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 1)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (skipFieldSpecX A lim)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withPreKeyInv (LibsignalCodeRoLoaded lsmpl) (bytesMergeExactRawSpecX A lim))) :
    PreKeyDecodeLoopF4OkWPlaced M A lim H :=
  fun _ _ _ _ _ _ _ _ _ fuel _ _ _ _ _ {_Qp} hfit hmax hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hfuel hlen =>
    sepWPp_anyQp_of_noPanic
      (sepWPp_mono_post (fun _ _ => preKeyLoopExitPostPlaced_mono_rem hmax)
        (preKeyStep_placed_wp hFrom hPush hSlow hvarint hint32 hskip hbytes
          (preKeyDecodeLoop_e4_placed hFrom hPush hSlow hvarint hint32 hskip hbytes fuel)
          (fitsEnv_sigLoop_mono_rem hmax hfit) hpc hrun hregs hx28 hx26 hx2 hsp hcl htr hfuel hlen))

theorem preKeyDecodeLoopF4W_of_callees_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) :
    PreKeyDecodeLoopF4OkWPlaced M A lim H :=
  preKeyDecodeLoopF4W_of_subroutines_placed_ok hC.decodeErrorFrom hC.decodeErrorPush
    hC.decodeVarintSlow hC.varintSlice hC.int32Merge hC.skipField hC.bytesMerge

private theorem lswb_ofNat64_cons_sub_one (b0 : BitVec 8) (bs : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs).length - 1#64 = BitVec.ofNat 64 bs.length := by
  simp only [List.length_cons]; bv_omega

theorem preKey_init_to_460_placed_wpW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {maxLen : Nat} {H : LibsignalHooks}
    (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced M A lim H)
    {sret sp' ptr : BitVec 64} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)}
    {s0 s2 : State} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (TryFromLoopEnv (2 * (bs1.length + 1) + 2) maxLen))
    (hmax : (b1 :: bs1).length ≤ maxLen)
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
        memRegion (sp' + 448#64) 64 ∗ A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100))
      (preKeyLoopExitPostPlaced A lim st maxLen SigTryFromCaps.zero
        s0 sp' sret (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
        (ptr + 1#64) (b1 :: bs1) (Pksm.decodeProto (b1 :: bs1)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  refine Wire.SepWPp.mono_pre
    (P' := (memRegion (sp' + 296#64) 152 ∗ A.pool lim st s2) ∗
      (((ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗ memRegion (sp' + 448#64) 64 ∗
        stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (prologue_80_init_placed_wpX (A := A) (lim := lim) (st := st)
      hst hpc hrun hx29 hx27 hx22 hx21 hx19 hx1) ?_
  intro s3 P3 hpc3 hrun3
    ⟨hst3, hpstate3, hx29_3, hx27_3, hx22_3, hx21_3, hx20_3, hx19_3, hx8_3, hx2_3, hent3⟩
  refine Wire.SepWPp.mono_pre (sepConj_mono_left hent3) ?_; clear hent3
  have hge2 : 2 ≤ (vb :: b1 :: bs1).length := by simp
  have hsub1 := lswb_ofNat64_cons_sub_one vb (b1 :: bs1)
  have hwire := Entails.trans
    (emptyPreKey_cells_entails_wirePreKeyOf A.repAlloc (sp' + 312#64))
    (wirePreKeyOf_empty_entails_loopCapsOf A.repAlloc (sp' + 312#64))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hwire
  refine Wire.SepWPp.mono_pre
    (P' := A.pool lim st s3 ∗ (sliceCursorAt (sp' + 296#64) (ptr + 1#64) (b1 :: bs1) ∗
      ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ memRegion (sp' + 448#64) 64 ∗
      stackAt sp' (skipFieldStackX 100) ∗
      wirePreKeyLoopCapsOf A.repAlloc (sp' + 312#64) SigTryFromCaps.zero Pksm.emptyProto))
    (by
      unfold sliceCursorAt; rw [hsub1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hwire)))))
      apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (prologue_bc_gt1_to_f4_placed_wpX (A := A) (lim := lim) (st := st)
      hge2 hlt hst3 hpc3 hrun3
      hpstate3 hx29_3 hx27_3 hx22_3 hx21_3 hx20_3 hx19_3 hx8_3 hx2_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨⟨hregs4, ⟨_, hsp4, hcl4, htr4⟩, hx28_4, hx26_4, hx2_4⟩, hent4⟩
  refine Wire.SepWPp.mono_pre (sepConj_mono_left hent4) ?_; clear hent4
  rw [hsub1] at hx2_4
  have hlt_body : (b1 :: bs1).length < 2 ^ 32 := by simp only [List.length_cons] at hlt ⊢; omega
  have hloop := hLoopF4 st maxLen SigTryFromCaps.zero s0 sp' sret
    (BitVec.ofNat 64 (vb :: b1 :: bs1).length) ptr vb
    bs1.length s4 (ptr + 1#64) b1 bs1 Pksm.emptyProto (Qp := noPanicQp s2)
    hfit hmax hpc4 hrun4 hregs4 hx28_4 hx26_4 hx2_4 hsp4 hcl4 htr4 (Nat.le_refl _) hlt_body
  dsimp only [Pksm.decodeProto]
  exact sepWPp_perm hloop (by apply entails_of_eq; sep_ac_rfl)

theorem preKey_earlyErr_to_504_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {x : RunCompose.PksmGhost} {s0 : State} {Qp : State → SepProp → Prop}
    (herr : x.bytes = [] ∨
      (∃ vb body, x.bytes = vb :: body ∧ ((vb >>> 4) < 3#8 ∨ 4#8 < (vb >>> 4) ∨ body = [])))
    (hlt : x.bytes.length < 2 ^ 32) (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s0.mem) (hx0 : s0.readReg64 .x0 = x.ptr)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length) (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 + 512#64) 96 ∗ A.pool lim st s0)
      (fun sf Pf => PostEpilogueStatePlaced s0 (s0.sp - 608#64) sf ∧ Pksm.pksmParse x.bytes = none ∧
        ∃ e : SignalProtocolError,
          Pf ⊢ pksmErrE A.repAlloc [] x.ret e ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion (s0.sp - 608#64) 296 ∗
            memRegion (s0.sp - 608#64 + 296#64) 152 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗ A.pool lim st sf)
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_; set sp' := s0.sp - 608#64
  rcases herr with hnil | ⟨vb, body, hcons, hcase⟩
  · have hx1_0 : s0.readReg64 .x1 = 0#64 := by rw [hx1, hnil]; rfl
    have hparse : Pksm.pksmParse x.bytes = none := by rw [hnil]; exact pksmParse_nil
    refine Wire.SepWPp.mono_pre
      (P' := (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ memRegion (sp' + 512#64) 96) ∗ A.pool lim st s0) ∗
        (memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152)) (by apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_frame_noPanic
      (prologue_nil_to_504_placed_wpE (A := A) (lim := lim) (st := st) hnil hpc hrun hsp hcl hx1_0 hx8) ?_
    intro sf Pf ⟨hstf, hentf⟩
    exact ⟨hstf, hparse, .ciphertextMessageTooShort 0,
      Entails.trans (sepConj_mono_left hentf) (by apply entails_of_eq; sep_ac_rfl)⟩
  · have hne : x.bytes ≠ [] := by rw [hcons]; simp
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion (sp' + 512#64) 96 ∗ A.pool lim st s0) ∗
        ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine sepWPp_bind_frame_noPanic
      (prologue_entry_ne_nil_placed_wpX (A := A) (lim := lim) (st := st) hne hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
    intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
    refine Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
    by_cases hlt3 : (vb >>> 4) < 3#8
    · have hvb30 : vb < 0x30#8 := by
        rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hlt3
        rw [BitVec.lt_def]; change vb.toNat / 16 < 3 at hlt3; change vb.toNat < 48; omega
      have hparse : Pksm.pksmParse x.bytes = none := by rw [hcons]; exact pksmParse_legacy hvb30
      refine Wire.SepWPp.mono_pre
        (P' := (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗ A.pool lim st s1) ∗
          (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine sepWPp_frame_noPanic
        (prologue_28_legacyVer_placed_wpE (A := A) (lim := lim) (st := st) hcons hlt3 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
      intro sf Pf ⟨hstf, hentf⟩
      exact ⟨hstf, hparse, .legacyCiphertextVersion (vb >>> 4),
        Entails.trans (sepConj_mono_left hentf) (by apply entails_of_eq; sep_ac_rfl)⟩
    · by_cases hgt4 : 4#8 < (vb >>> 4)
      · have hvb4f : 0x4f#8 < vb := by
          have hvb_lt := vb.isLt
          rw [BitVec.lt_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hgt4
          rw [BitVec.lt_def]; change 4 < vb.toNat / 16 at hgt4; change 79 < vb.toNat; omega
        have hparse : Pksm.pksmParse x.bytes = none := by rw [hcons]; exact pksmParse_unrec hvb4f
        refine Wire.SepWPp.mono_pre
          (P' := (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248) ∗ A.pool lim st s1) ∗
            (preKeyCalleeSavedAt sp' s0 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by apply entails_of_eq; sep_ac_rfl) ?_
        refine sepWPp_frame_noPanic
          (prologue_28_unrecognizedVer_placed_wpE (A := A) (lim := lim) (st := st)
            hcons hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx19_1) ?_
        intro sf Pf ⟨hstf, hentf⟩
        exact ⟨hstf, hparse, .unrecognizedCiphertextVersion (vb >>> 4),
          Entails.trans (sepConj_mono_left hentf) (by apply entails_of_eq; sep_ac_rfl)⟩
      · have hbody : body = [] := hcase.elim (fun h => absurd h hlt3) (fun h => h.elim (fun h => absurd h hgt4) id)
        have hparse : Pksm.pksmParse x.bytes = none := by rw [hcons, hbody]; exact pksmParse_bkNone decodeProto_nil rfl
        have hbytes1 : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) := by rw [hcons, hbody, pointsToBytes_singleton]
        refine Wire.SepWPp.mono_pre
          (P' := ((x.ptr ↦₈ vb) ∗ A.pool lim st s1) ∗
            (preKeyCalleeSavedAt sp' s0 ∗ memRegion x.ret 248 ∗ memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152))
          (by rw [← hbytes1]; apply entails_of_eq; sep_ac_rfl) ?_
        refine sepWPp_bind_frame_noPanic
          (prologue_28_validVer_placed_wpX (A := A) (lim := lim) (st := st)
            hlt3 hgt4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
        intro s2 P2 hpc2 hrun2 ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
        refine Wire.SepWPp.mono_pre (sepConj_mono_left hent2) ?_; clear hent2
        have hx1_2' : s2.readReg64 .x1 = 1#64 := by rw [hx1_2, hcons, hbody]; rfl
        refine Wire.SepWPp.mono_pre
          (P' := (memRegion (sp' + 296#64) 152 ∗ A.pool lim st s2) ∗
            ((x.ptr ↦ₛ x.bytes) ∗ preKeyCalleeSavedAt sp' s0 ∗ memRegion x.ret 248 ∗ memRegion sp' 296))
          (by rw [← hbytes1]; apply entails_of_eq; sep_ac_rfl) ?_
        refine sepWPp_bind_frame_noPanic
          (prologue_80_init_placed_wpX (A := A) (lim := lim) (st := st)
            hst2 hpc2 hrun2 hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
        intro s3 P3 hpc3 hrun3 ⟨hst3, hpstate3, hx29_3, hx27_3, _, _, _, hx19_3, _, _, hent3⟩
        refine Wire.SepWPp.mono_pre (sepConj_mono_left hent3) ?_; clear hent3
        refine Wire.SepWPp.mono_pre
          (P' := (memRegion x.ret 248 ∗ memRegion sp' 296 ∗ ((sp' + 296#64) ↦₆₄ (x.ptr + 1#64)) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
            (((sp' + 312#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 320#64) 16 ∗
              ((sp' + 336#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 344#64) 16 ∗
              ((sp' + 360#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 368#64) 16 ∗
              ((sp' + 384#64) ↦₆₄ noneCap) ∗ memRegion (sp' + 392#64) 16 ∗
              ((sp' + 408#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 412#64) 4 ∗
              ((sp' + 416#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 420#64) 4 ∗
              ((sp' + 424#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 428#64) 4 ∗
              ((sp' + 432#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 436#64) 4) ∗
            ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ A.pool lim st s3) ∗ ((x.ptr ↦ₛ x.bytes) ∗ preKeyCalleeSavedAt sp' s0))
          (by simp only [BitVec.sub_self]; apply entails_of_eq; sep_ac_rfl) ?_
        refine sepWPp_frame_noPanic
          (prologue_bc_len1_to_504_placed_wpE (A := A) (lim := lim) (st := st) (ptr := x.ptr)
            hst3 hpc3 hrun3 hpstate3 hx29_3 hx27_3 hx19_3) ?_
        intro sf Pf ⟨hstf, hentf⟩
        exact ⟨hstf, hparse, .invalidProtobufEncoding,
          Entails.trans (sepConj_mono_left hentf) (by apply entails_of_eq; sep_ac_rfl)⟩

theorem preKey_valid_to_460_placed_wpW [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hLoopF4 : PreKeyDecodeLoopF4OkWPlaced M A lim H)
    {x : RunCompose.PksmGhost} {vb b1 : BitVec 8} {bs1 : List (BitVec 8)} {s0 : State} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (TryFromLoopEnv (2 * (x.bytes.length - 1) + 2) x.bytes.length))
    (hcons : x.bytes = vb :: b1 :: bs1) (hge3 : ¬ (vb >>> 4) < 3#8) (hle4 : ¬ 4#8 < (vb >>> 4))
    (hlt : x.bytes.length < 2 ^ 32) (hpc : s0.pc = (blkPl_111).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true) (hcl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.ptr) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1120#64) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (s0.sp - 608#64 + 296#64) 152 ∗ memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        memRegion (s0.sp - 608#64 + 512#64) 96 ∗ A.pool lim st s0 ∗ stackAt (s0.sp - 608#64) (skipFieldStackX 100))
      (fun sf Pf =>
        PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr vb sf ∧
        ∃ evs : List AllocEvent,
          TryFromLoopEnv (2 * (x.bytes.length - 1) + 2) x.bytes.length evs ∧
          (Pf ⊢ (x.ptr ↦₈ vb) ∗
            preKeyLoopExitMem (A.atState lim (M.stepEvents evs st) sf)
              (s0.sp - 608#64) (x.ptr + 1#64) (b1 :: bs1) (sf.readReg64 .x24) (Pksm.decodeProto (b1 :: bs1)) ∗
            preKeyCalleeSavedAt (s0.sp - 608#64) s0))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_; set sp' := s0.sp - 608#64
  have hne : x.bytes ≠ [] := by rw [hcons]; simp
  have hfit' : FitsEnv M lim st (TryFromLoopEnv (2 * (bs1.length + 1) + 2) x.bytes.length) := hfit
  have hmax : (b1 :: bs1).length ≤ x.bytes.length := by rw [hcons]; simp
  refine Wire.SepWPp.mono_pre
    (P' := (memRegion (sp' + 512#64) 96 ∗ A.pool lim st s0) ∗
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (prologue_entry_ne_nil_placed_wpX (A := A) (lim := lim) (st := st) hne hlt hpc hrun hsp hcl hx0 hx1 hx8) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hx0_1, hx1_1, hx19_1, hx29_1, hent1⟩
  refine Wire.SepWPp.mono_pre (sepConj_mono_left hent1) ?_; clear hent1
  have hbytes : (x.ptr ↦ₛ x.bytes) = (x.ptr ↦₈ vb) ∗ ((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) := by rw [hcons, pointsToBytes_cons]
  refine Wire.SepWPp.mono_pre
    (P' := ((x.ptr ↦₈ vb) ∗ A.pool lim st s1) ∗
      (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗ preKeyCalleeSavedAt sp' s0 ∗
        memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗ stackAt sp' (skipFieldStackX 100)))
    (by rw [hbytes]; apply entails_of_eq; sep_ac_rfl) ?_
  refine sepWPp_bind_frame_noPanic
    (prologue_28_validVer_placed_wpX (A := A) (lim := lim) (st := st)
      hge3 hle4 hst1 hpc1 hrun1 hx0_1 hx1_1 hx19_1 hx29_1) ?_
  intro s2 P2 hpc2 hrun2 ⟨hst2, hx29_2, hx27_2, hx22_2, hx21_2, hx19_2, hx1_2, hent2⟩
  refine Wire.SepWPp.mono_pre (sepConj_mono_left hent2) ?_; clear hent2
  refine Wire.SepWPp.mono_pre
    (P' := (((x.ptr + 1#64) ↦ₛ (b1 :: bs1)) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 448#64) 64 ∗
        A.pool lim st s2 ∗ stackAt sp' (skipFieldStackX 100)) ∗ ((x.ptr ↦₈ vb) ∗ preKeyCalleeSavedAt sp' s0))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  have hlt' : (vb :: b1 :: bs1).length < 2 ^ 32 := by rwa [← hcons]
  have hx1_2' : s2.readReg64 .x1 = BitVec.ofNat 64 (vb :: b1 :: bs1).length := by rwa [← hcons]
  refine sepWPp_frame_noPanic
    (preKey_init_to_460_placed_wpW hLoopF4 hfit' hmax hlt' hst2 hpc2 hrun2
      hx29_2 hx27_2 hx22_2 hx21_2 hx19_2 hx1_2') ?_
  intro sf Pf ⟨hstf, evs, hevs, hentf⟩
  rw [← hcons] at hstf
  exact ⟨hstf, evs, hevs, Entails.trans (sepConj_mono_left hentf) (by apply entails_of_eq; sep_ac_rfl)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.LoopStepWPlacedBudget
