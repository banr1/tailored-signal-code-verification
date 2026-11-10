/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedB
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Post-Loop Part B

Proves panic-free `RustCliAllocBudget M` specifications for post-loop Segments 2, 3, 4-error, and
4-ok packing (`+1668 .. +2648` → `+1284`) of Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet.Wire
  CryptoVerification.E2E.Pqxdh.ResponderWire
open CryptoGames.LibsignalSession (
  PublicKey SignalMessage SignalProtocolError
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks lsmpl lsRustDeallocSym blkPl_111 blkPl_116
  LibsignalCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecHeader vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  VecArg TryFromGhost intoBoxedSliceStack boxU8Buf smallRootStack logOff lsLogOff
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SignalMessageGhost errTag errResultAt signalMessageResultAt
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue (
  msgWords15At msgHeapAt
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
)
open CryptoVerification.LibsignalTripleRatchet.Wire (
  SepWPp SepWPp.pure_pre SepWPp.mono_pre
  tryFromPlacedImg logOff_tryFromPlacedImg
  vecU8Buf vecU8Buf_zero vecU8At_eq_header_buf vecHeader_entails_memRegion24
  memRegion_four_entails stackAt_sub_split entails_of_eq cap_add1_eq_of_lt
  layoutOk_align1
  pkBytesOf pkLayoutAt pkRestAt sevenBytesHeadAt sevenBytesTailAt
  sevenBytesHeadAt_eq_tailAt pkLayoutAt_eq_pointsToBytes memRegion32_entails_pkLayoutAt
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  zeroExtend32_lsr4_truncate8
)
open CryptoVerification.E2E.Pqxdh.ResponderWire (
  PreKeyTryFromArgs opkTag preKeyResultAt preKeyPlacedProg
  KeepsFrozenInv withPreKeyInv ls_subroutine_ok_pk_of_cl SepWPp.of_sepWP_pk
  PreKeyPostState PreKeyPostState.of_steps
  vecU8Rest vecU8Buf_to_slice_rest slice_rest_to_vecU8Buf
  deserialize_djb_ok spUnused112 memRegion32_112_unpack deser_ok_entails_vecHeader_region
  memRegion32_words4 words5_memRegion8_72_entails_120
  speAt_tryFrom_words2 boxU8Buf_kyber_dealloc memRegion48_words6
  words6_entails_memRegion48 words7_memRegion64_entails_memRegion120
  err_result_entails_preKeyResultAt memRegion248_split_err
  memRegion120_words15 memRegion48_mid_eq memRegion48_tail_eq memRegion248_sret_split
  words14_entails_memRegion112 sevenBytesHead_tail_assoc preKeyResultAt_ok_intro
  opkTag_mask64_truncate32
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56
  bv_sub_add_lit' bv_sub_sub_lit
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget RustLayoutOk
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (
  LsRetAddr624 lsRetAddr624_blockPlacement_base_add
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  IntoBoxedSliceEnv intoBoxedSliceEvents intoBoxedSliceSpec intoBoxedSliceSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (
  TryFromEnvGen tryFromPlacedSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget (TryFromPostEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (
  PreKeySeg2Env identityKeyTryFromSliceOkPlacedSpec identityKeyTryFromSlice_placed_ok
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp freeOnly_rustDeallocEvents
  SepWPp.of_sepWP_end_noPanic_pk SepWPp.let_state SepWPp.frame_noPanic_pk
  SepWPp.call_noPanic_budget_pk PreKeyDeallocOk
  cleanup_568_placed_wp cleanup_558_placed_wp cleanup_554_placed_wp
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8

/-! ## Callee Predicates and `SignalMessage::try_from` Envelope Bridge -/

/-- Pointer-independent allocator event envelope of `<SignalMessage as TryFrom<&[u8]>>::try_from`
on input slice `bs`, parameterized by the inner post-loop envelope `postEnv`. -/
def SigTryFromEnv (postEnv : List (BitVec 8) → List AllocEvent → Prop)
    (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  TryFromEnvGen (fun g => postEnv g.bytes) ⟨0#64, bs, 0#64⟩

/-- Concrete allocator event envelope of `<SignalMessage as TryFrom<&[u8]>>::try_from`
on input slice `bs`, instantiating `SigTryFromEnv` with `TryFromPostEnv`. -/
abbrev SigTryFromConcreteEnv : List (BitVec 8) → List AllocEvent → Prop :=
  SigTryFromEnv TryFromPostEnv

theorem tryFromEnvGen_eq_sigTryFromEnv
    (postEnv : List (BitVec 8) → List AllocEvent → Prop)
    (bytesA : BitVec 64) (bs : List (BitVec 8)) (ret : BitVec 64) :
    TryFromEnvGen (fun g => postEnv g.bytes) ⟨bytesA, bs, ret⟩ =
      SigTryFromEnv postEnv bs := by
  funext evs; apply propext; constructor <;> intro h <;> cases h
  · exact .nil
  · exact .loopOnly ‹_›
  · exact .loopPost ‹_› ‹_›
  · exact .nil
  · exact .loopOnly ‹_›
  · exact .loopPost ‹_› ‹_›

def PreKeyIntoBoxOk [LibsignalPlacement] (Inv : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 56)
    (withPreKeyInv Inv (intoBoxedSliceSpec M A lim))

def PreKeySigTryFromOkGen [LibsignalPlacement] (Inv : Memory → Prop)
    (postEnv : List (BitVec 8) → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 85)
    (withPreKeyInv Inv (tryFromPlacedSpecGen (fun g => postEnv g.bytes) A lim))

abbrev PreKeySigTryFromOk [LibsignalPlacement] (Inv : Memory → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  PreKeySigTryFromOkGen Inv TryFromPostEnv A lim H

private theorem vecU8Buf_len_le_cap (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜bs.length ≤ cap.toNat⌝ ∗ vecU8Buf A cap ptr bs := by
  apply entails_of_eq
  unfold vecU8Buf
  rw [pure_sepConj_pure_assoc]
  congr 2
  exact propext ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩

/-! ## Segment 2 (`+1668 .. +1788` → `+2096`) -/

theorem post_seg2_1b4_to_360_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hIntoBox : PreKeyIntoBoxOk Inv A lim H)
    {x : PreKeyTryFromArgs} (hfits : FitsEnv M lim st (PreKeySeg2Env x))
    {s0 s : State}
    {sp' kyberCap kyberPtr ikCap msgCap : BitVec 64} {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running) (hky_lt : kyberCap.toNat < 2 ^ 63)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberCap)
    (hx27 : s.readReg64 .x27 = 0x8000000000000002#64) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberPtr) (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64) (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length) (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2096#64) s
      (memRegion (sp' + 12#64) 4 ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 112#64) 32 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' +
        313#64) ↦ₛ x.baseKey.toList) ∗ memRegion (sp' + 345#64) 15 ∗
        vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗ A.pool lim st s ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, PreKeySeg2Env x evs ∧
        ∃ kyberBoxPtr : BitVec 64,
          PreKeyPostState Inv s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧
          sf.readReg64 .x28 = kyberBoxPtr ∧
          sf.readReg64 .x27 = 0x8000000000000002#64 ∧ sf.readReg64 .x26 = msgCap ∧
          sf.readReg64 .x25 = 1569#64 ∧
          sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 =
          0x44#64 ∧ sf.readReg64 .x21 = x.ptr ∧
          sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
          (Pf ⊢ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' +
          68#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' +
            120#64) ↦₈ b31) ∗
            ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' +
            136#64) b0 b1 b2 b3 b4 b5 b6 ∗
            memRegion (sp' + 312#64) 48 ∗ boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hky_eq := cap_add1_eq_of_lt hky_lt
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStack smallRootStack (by decide) (by decide)
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (vecU8Buf_len_le_cap A.repAlloc kyberCap kyberPtr x.kyberBytes)))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hky_ge_raw => ?_
  have hky_ge : 1569 ≤ kyberCap.toNat := by
    simpa [PreKeyTryFromArgs.kyberBytes_length] using hky_ge_raw
  have hseg2_evs :
      PreKeySeg2Env x (intoBoxedSliceEvents ⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩) :=
    ⟨kyberCap, hky_ge, hky_lt, rfl⟩
  have hfits_box :
      FitsEnv M lim st (IntoBoxedSliceEnv ⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩) :=
    fun evs hevs => hfits evs (hevs ▸ hseg2_evs)
  rw [hpk, ← pkLayoutAt_eq_pointsToBytes]
  refine SepWPp.mono_pre
    (sepConj_mono (memRegion_four_entails (sp' + 12#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (memRegion32_112_unpack sp')))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w112 => SepWPp.exists_pre fun b120 =>
    SepWPp.exists_pre fun w128 => SepWPp.exists_pre fun w132 =>
    SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun w12 => ?_
  dsimp only [pkLayoutAt]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 1680#64) ?_
  dsimp only [sevenBytesHeadAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1680#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
      A.pool lim st _ ∗ stackAt sp' smallRootStack)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv1 (mid := (blkPl_111).base + 1704#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1704#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv2 => ?_⟩
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
      A.pool lim st _ ∗ stackAt sp' smallRootStack)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := (blkPl_111).base + 1768#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_sync_111 ((blkPl_111).base + 1768#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv3 => ?_⟩
  have h136_head := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6
  have hcollapse :=
    deser_ok_entails_vecHeader_region sp' b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31
  refine SepWPp.mono_pre (P' := (∃∗ w320 : BitVec 64, ∃∗ w328 : BitVec 64,
        ((sp' + 312#64) ↦₆₄ (b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8)) ∗ ((sp' +
        320#64) ↦₆₄ w320) ∗ ((sp' + 328#64) ↦₆₄ w328) ∗
        memRegion (sp' + 336#64) 24) ∗ ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' +
        40#64) ↦₆₄ 1569#64) ∗
      ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗ ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' +
        132#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes ∗
      A.pool lim st _ ∗ stackAt sp' smallRootStack)
    (by
      rw [h136_head]
      dsimp only [sevenBytesTailAt]
      refine Entails.trans ?_ (sepConj_mono_left hcollapse)
      dsimp only [sevenBytesHeadAt, pkRestAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; sep_ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w320 => SepWPp.exists_pre fun w328 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv3 (mid := lsmpl.base 56) ?_
  wp_steps_sync_111 (lsmpl.base 56)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv4 => ?_⟩
  refine SepWPp.let_state ?_; intro sc
  have hvec_ky : vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ 1569#64) ∗ vecU8Buf A.repAlloc kyberCap kyberPtr x.kyberBytes := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [PreKeyTryFromArgs.kyberBytes_length, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩ : VecArg), st) hIntoBox
    (by simp_all [sc, arm64_norm]) (by simp_all [sc, arm64_norm])
    (by dsimp only [sc]; simpa [State.spAligned, arm64_norm] using hsp) hinv4
    (ret_pc := (blkPl_111).base + 1780#64) (by simp_all [sc, arm64_norm])
    (T := vecU8At A.repAlloc (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
      A.pool lim st sc ∗ stackAt sp' intoBoxedSliceStack)
    (φ := sp' + 312#64 = sp' + 312#64 ∧
      FitsEnv M lim st (IntoBoxedSliceEnv ⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩))
    (by simp_all [sc, intoBoxedSliceSpec, intoBoxedSliceSpecWithStack, VecArg.at,
      intoBoxedSliceStack, arm64_norm])
    ⟨rfl, hfits_box⟩
    (by rw [hvec_ky, hstackBox]; sep_focus)
    ?_
  intro s5 hpc5 hrun5 hsp5 hsp5_align hinv5 hcs5
  dsimp only [intoBoxedSliceSpec, intoBoxedSliceSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx1_5, htr5⟩ => ?_
  simp only [PreKeyTryFromArgs.kyberBytes_length] at hx1_5
  have hsc_sp : sc.sp = sp' := by simp [sc, hsp_eq, arm64_norm]
  rw [hsc_sp] at hsp5 ⊢
  rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hv25_5, hx26_5, hx27_5, hv28_5,
    hx29_5, hv_5⟩
  clear hv25_5 hv28_5 hv_5
  dsimp only [sc] at htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx26_5 hx27_5 hx29_5
  simp only [htr, hx29, hx27, hx26, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx26_5 hx27_5 hx29_5
  clear hsc_sp
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv5 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2096#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv6 => ?_⟩
  refine ⟨intoBoxedSliceEvents ⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩, hseg2_evs,
    s5.readReg64 .x0,
    ⟨by simp [hsp5, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp5_align,
      hinv6, by simp [htr5, arm64_norm]⟩,
    by simp [hx29_5, arm64_norm],
    by simp [arm64_norm],
    by simp [hx27_5, arm64_norm],
    by simp [hx26_5, arm64_norm],
    by simp [arm64_norm],
    by simp [hx24_5, arm64_norm],
    by simp [hx23_5, arm64_norm],
    by simp [hx22_5, arm64_norm],
    by simp [hx21_5, arm64_norm],
    by simp [hx20_5, arm64_norm],
    by simp [hx19_5, arm64_norm], ?_⟩
  have h48 : vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 x.kyberBytes.length) ∗
      memRegion (sp' + 336#64) 24 ⊢ memRegion (sp' + 312#64) 48 := by
    rw [show (48 : Nat) = 24 + 24 by decide, memRegion_split (sp' + 312#64) 24 24 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (vecHeader_entails_memRegion24 (sp' + 312#64) kyberCap kyberPtr _)
  refine Entails.trans
    (Q := (vecHeader (sp' + 312#64) kyberCap kyberPtr (BitVec.ofNat 64 x.kyberBytes.length) ∗
      memRegion (sp' + 336#64) 24) ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' +
        68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗ spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' +
        120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗ sevenBytesHeadAt (sp' +
        136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        boxU8Buf A.repAlloc (s5.readReg64 .x0) x.kyberBytes ∗
        A.pool lim (M.stepEvents (intoBoxedSliceEvents ⟨sp' + 312#64, kyberCap, kyberPtr,
          x.kyberBytes⟩) st) _ ∗
        stackAt sp' smallRootStack))
    (by
      rw [hstackBox]
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.boxU8Buf]
      simp only [intoBoxedSliceStack, smallRootStack, arm64_norm]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left h48) ?_
  dsimp only [sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; sep_ac_rfl

/-! ## Segment 3 (`+2096 .. +2168`) -/

theorem post_seg3_360_to_3a8_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {postEnv : List (BitVec 8) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hSigTryFrom : PreKeySigTryFromOkGen Inv postEnv A lim H)
    {x : PreKeyTryFromArgs} (hfits : FitsEnv M lim st (SigTryFromEnv postEnv x.inner))
    {s0 s : State} {sp' kyberBoxPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {ik0 ik1 ik2 ik3 : BitVec 64} (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hlt_in : x.inner.length < 2 ^ 32) (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2096#64)
    (hrun : s.status = .Running) (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
        52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗
        vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ lsLogOff ∗ A.pool lim st s ∗
        stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, SigTryFromEnv postEnv x.inner evs ∧
        PreKeyPostState Inv s0 sp' sf ∧ sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 =
        kyberBoxPtr ∧
        sf.readReg64 .x27 = x.regId.zeroExtend 64 ∧ sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 =
        1569#64 ∧
        sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧ sf.readReg64 .x22 = 0x44#64 ∧
        sf.readReg64 .x21 = x.ptr ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length ∧ sf.readReg64 .x19 = x.sret ∧
        (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗
        ((sp' + 52#64) ↦₃₂ x.regId) ∗
          ((sp' + 56#64) ↦₃₂ x.regId) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗ ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' +
          168#64) ↦₆₄ ik3) ∗
          signalMessageResultAt A.repAlloc [] (sp' + 312#64)
            (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ lsLogOff ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hcallIk := ls_subroutine_ok_pk_of_cl
    (callerProg := preKeyPlacedProg H) hcl_of_inv (identityKeyTryFromSlice_placed_ok H)
  have hblk116 : (blkPl_116).base = lsmpl.base 116 := rfl
  rw [hblk116] at hcallIk
  have hstackIk := stackAt_sub_split sp' 96 smallRootStack (by decide) (by decide)
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using memRegion_split (sp' + 312#64) 40 8 (by decide)
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
      52#64) ↦₃₂ x.regId) ∗
      ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
      (ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
    (by
      rw [h48_split]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (vecU8Buf_to_slice_rest A.repAlloc ikCap ikPtr x.ikBytes)))))))))))) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 116) ?_
  wp_steps_sync_111 (lsmpl.base 116)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  refine SepWPp.let_state ?_; intro sc1
  have hik_deser : PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩ := deserialize_djb_ok x.idPub
  have hik_len : (33#64 : BitVec 64).toNat = x.ikBytes.length := by simp
  refine SepWPp.call_noPanic_budget_pk hkf (ikPtr, x.ikBytes, ⟨x.idPub⟩, sp' + 312#64) hcallIk
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by dsimp only [sc1]; simpa [State.spAligned, arm64_norm] using hsp) hinv1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp_all [sc1, arm64_norm])
    (T := (ikPtr ↦ₛ x.ikBytes) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ (33#64 : BitVec 64).toNat = x.ikBytes.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩)
    (by simp_all [sc1, identityKeyTryFromSliceOkPlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec, arm64_norm])
    ⟨rfl, hik_len, rfl, hik_deser⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [identityKeyTryFromSliceOkPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_pre fun hvm2 => SepWPp.pure_pre fun htr2 => ?_
  have hpool2 : A.pool lim st sc1 = A.pool lim st s2 :=
    (A.pool_transport lim st sc1 s2 hvm2).symm
  rw [hpool2]; clear hvm2 hpool2
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  rw [hsc1_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, hv_2⟩
  clear hv_2
  dsimp only [sc1] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [htr, hx29, hx28, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19, arm64_norm]
    at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  clear hsc1_sp
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) 33#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  have hrepack_ik := slice_rest_to_vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes
  refine SepWPp.mono_pre
    (P' := (∃∗ w144 : BitVec 64, ∃∗ w152 : BitVec 64, ∃∗ w160 : BitVec 64, ∃∗ w168 : BitVec 64,
        ((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗ ((sp' + 160#64) ↦₆₄ w160) ∗ ((sp' +
        168#64) ↦₆₄ w168)) ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
        52#64) ↦₃₂ x.regId) ∗
      ((sp' + 56#64) ↦₃₂ 33#32) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦₆₄ ik0) ∗ ((sp' +
        328#64) ↦₆₄ ik1) ∗
      ((sp' + 336#64) ↦₆₄ ik2) ∗ ((sp' + 344#64) ↦₆₄ ik3) ∗ memRegion (sp' + 352#64) 8 ∗
        memRegion (sp' + 360#64) 72 ∗
      vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗ (msgPtr ↦ₛ x.inner) ∗
        vecU8Rest A.repAlloc msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool lim st s2 ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split, memRegion32_words4 (sp' + 144#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hik (sp' + 320#64)]
      simp only [hstackIk,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
      refine Entails.sepExists_elim fun w168 => Entails.sepExists_elim fun w160 =>
        Entails.sepExists_elim fun w152 => Entails.sepExists_elim fun w144 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro w144)
      refine Entails.trans ?_ (Entails.sepExists_intro w152)
      refine Entails.trans ?_ (Entails.sepExists_intro w160)
      refine Entails.trans ?_ (Entails.sepExists_intro w168)
      refine Entails.trans
        (Q := ((ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A.repAlloc ikCap ikPtr x.ikBytes) ∗
          vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          (((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗ ((sp' + 160#64) ↦₆₄ w160) ∗
          ((sp' + 168#64) ↦₆₄ w168) ∗
            ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
            52#64) ↦₃₂ x.regId) ∗
            ((sp' + 56#64) ↦₃₂ 33#32) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦₆₄ ik0) ∗ ((sp' +
            328#64) ↦₆₄ ik1) ∗
            ((sp' + 336#64) ↦₆₄ ik2) ∗ ((sp' + 344#64) ↦₆₄ ik3) ∗ memRegion (sp' + 352#64) 8 ∗
            memRegion (sp' + 360#64) 72 ∗ lsLogOff ∗ A.pool lim st s2 ∗ (memRegion (sp' -
            BitVec.ofNat 64 smallRootStack) (smallRootStack - 96) ∗ stackAt sp' 96)))
        (by simp only [smallRootStack, arm64_norm]; apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono hrepack_ik
          (sepConj_mono_left (vecU8Buf_to_slice_rest A.repAlloc msgCap msgPtr x.inner))) ?_
      simp only [smallRootStack, arm64_norm]; apply entails_of_eq; sep_ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 =>
    SepWPp.exists_pre fun w160 => SepWPp.exists_pre fun w168 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := lsmpl.base 85) ?_
  wp_steps_sync_111 (lsmpl.base 85)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv3 => ?_⟩
  refine SepWPp.let_state ?_; intro sc2
  have h120 := words5_memRegion8_72_entails_120 sp' 0xfffffffffffffffe#64 ik0 ik1 ik2 ik3
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗ (msgPtr ↦ₛ x.inner) ∗
      vecU8Rest A.repAlloc msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool lim st sc2 ∗ stackAt sp' smallRootStack ∗
      ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
      ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗ ((sp' +
        60#64) ↦₃₂ 0#32) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes)
    (by
      dsimp only [sc2]
      refine Entails.trans ?_ (sepConj_mono_left h120)
      apply entails_of_eq; sep_ac_rfl) ?_
  have hin_toNat : (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length :=
    Nat.mod_eq_of_lt (by omega)
  have hlog_eq : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  have hfits_sig :
      FitsEnv M lim st
        (TryFromEnvGen (fun g => postEnv g.bytes) ⟨msgPtr, x.inner, sp' + 312#64⟩) := by
    rw [tryFromEnvGen_eq_sigTryFromEnv]
    exact hfits
  refine SepWPp.call_noPanic_budget_pk hkf
    ((⟨msgPtr, x.inner, sp' + 312#64⟩ : TryFromGhost), st) hSigTryFrom
    (by simp_all [sc2, arm64_norm]) (by simp_all [sc2, arm64_norm])
    (by dsimp only [sc2]; simpa [State.spAligned, arm64_norm] using hsp2_align) hinv3
    (ret_pc := (blkPl_111).base + 2168#64) (by simp_all [sc2, arm64_norm])
    (T := (msgPtr ↦ₛ x.inner) ∗ memRegion (sp' + 312#64) 120 ∗ logOff tryFromPlacedImg ∗
      stackAt sp' smallRootStack ∗ A.pool lim st sc2)
    (φ := msgPtr = msgPtr ∧
      (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length ∧
      x.inner.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64 ∧
      FitsEnv M lim st
        (TryFromEnvGen (fun g => postEnv g.bytes) ⟨msgPtr, x.inner, sp' + 312#64⟩))
    (by simp_all [sc2, tryFromPlacedSpecGen, arm64_norm])
    ⟨rfl, hin_toNat, hlt_in, rfl, hfits_sig⟩ (by rw [hlog_eq]; sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hinv4 hcs4
  dsimp only [tryFromPlacedSpecGen]
  simp only [hlog_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evs => SepWPp.pure_pre fun htr4 => ?_
  refine SepWPp.pure_pre fun hevs => ?_
  rw [tryFromEnvGen_eq_sigTryFromEnv] at hevs
  have hsc2_sp : sc2.sp = sp' := by simp [sc2, hsp2, arm64_norm]
  rw [hsc2_sp] at hsp4 ⊢
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4, hv_4⟩
  clear hv_4
  dsimp only [sc2] at htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  simp only [htr2, hx29_2, hx28_2, hx27_2, hx26_2, hx25_2, hx24_2, hx23_2, hx22_2, hx21_2, hx20_2,
    hx19_2, arm64_norm]
    at htr4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  clear hsc2_sp
  refine SepWPp.of_sepWP_end_noPanic_pk hkf hinv4 ?_
  refine ProofLib.SepWP.done hpc4 hrun4 ⟨inferInstance, fun hinv5 => ?_⟩
  refine ⟨evs, hevs, ⟨hsp4, hsp4_align, hinv5, htr4⟩,
    hx29_4, hx28_4, hx27_4, hx26_4, hx25_4, hx24_4, hx23_4, hx22_4, hx21_4, hx20_4, hx19_4, ?_⟩
  have hrepack_msg := slice_rest_to_vecU8Buf A.repAlloc msgCap msgPtr x.inner
  refine Entails.trans
    (Q := ((msgPtr ↦ₛ x.inner) ∗ vecU8Rest A.repAlloc msgCap msgPtr x.inner) ∗
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        lsLogOff ∗ stackAt sp' smallRootStack ∗ A.pool lim (M.stepEvents evs st) s4 ∗ ((sp' +
        32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 60#64) ↦₃₂ 0#32) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗ ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; sep_ac_rfl

/-! ## Segment 4 Error Path (`+2168 .. +2648` → `+1284`) -/

theorem post_seg4_err_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {e : SignalProtocolError}
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .error e)
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 176#64) 48 ∗
        signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion x.sret 248 ∗ boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗ vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A.repAlloc x.sret x ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 312#64) 120 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (boxU8Buf_kyber_dealloc A.repAlloc kyberBoxPtr x))))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hky_ne => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (speAt_tryFrom_words2 A.repAlloc (sp' + 320#64) hsig)))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew0 => SepWPp.exists_pre fun ew1 => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hpack => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (entails_of_eq (memRegion32_words4 (sp' + 336#64)))))))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew5 => SepWPp.exists_pre fun ew4 =>
    SepWPp.exists_pre fun ew3 => SepWPp.exists_pre fun ew2 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion48_words6 (sp' + 176#64)))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun t5 => SepWPp.exists_pre fun t4 =>
    SepWPp.exists_pre fun t3 => SepWPp.exists_pre fun t2 =>
    SepWPp.exists_pre fun t1 => SepWPp.exists_pre fun t0 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (entails_of_eq (memRegion248_split_err x.sret))))))))))))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun s0_6 => SepWPp.exists_pre fun s0_5 =>
    SepWPp.exists_pre fun s0_4 => SepWPp.exists_pre fun s0_3 =>
    SepWPp.exists_pre fun s0_2 => SepWPp.exists_pre fun s0_1 =>
    SepWPp.exists_pre fun s0_0 => ?_
  have hky_beq : (kyberBoxPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hky_ne
  have hlay1569 : RustLayoutOk 1569 1 := ⟨layoutOk_align1 (by decide) (by decide), by decide⟩
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps_sync_111 ((blkPl_111).ρ lsRustDeallocSym)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  rw [RustCliAllocBudget.repAlloc_live_norm]
  refine SepWPp.let_state ?_; intro sc
  refine SepWPp.call_noPanic_budget_pk hkf (kyberBoxPtr, 1569, 1, st) hdealloc
    (by simp_all [sc, arm64_norm]) (by simp_all [sc, arm64_norm])
    (by dsimp only [sc]; tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2596#64) (by simp_all [sc, arm64_norm])
    (T := A.pool lim st sc ∗ A.live kyberBoxPtr 1569 1 ∗ memRegion kyberBoxPtr 1569 ∗
      stackAt sp' allocHookStack)
    (φ := kyberBoxPtr = kyberBoxPtr ∧ (1569#64 : BitVec 64).toNat = 1569 ∧
      (1#64 : BitVec 64).toNat = 1 ∧ LsRetAddr624 ((blkPl_111).base + 2596#64))
    (by simp_all [sc, rustCliDeallocBudgetSpec, arm64_norm])
    ⟨rfl, rfl, rfl, lsRetAddr624_blockPlacement_base_add 111 2596#64 (by decide) (by decide)⟩
    (by rw [hstack]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [rustCliDeallocBudgetSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hpres2, _⟩ => ?_
  have hsc_sp : sc.sp = sp' := by simp [sc, hsp_eq, arm64_norm]
  rw [hsc_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hv19, hv20, hv21, hv22, hx23_2, hv24, hv25, hx26_2, hv27, hv28, hv29, hv_2⟩
  clear hv19 hv20 hv21 hv22 hv24 hv25 hv27 hv28 hv29 hv_2
  have htr2 : s2.trace = s0.trace := by simp [hpres2.2, sc, htr, arm64_norm]
  dsimp only [sc] at hx23_2 hx26_2
  simp only [hx23, hx26, arm64_norm] at hx23_2 hx26_2
  clear hpres2 hsc_sp
  set st1 := M.stepEvents (rustDeallocEvents 1569 1) st
  have herr_res := err_result_entails_preKeyResultAt A.repAlloc x hsig ew0 ew1 ew2 ew3 ew4 ew5 hpack
  have hm48 :
      ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗ ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' +
        200#64) ↦₆₄ ew3) ∗
      ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ⊢
        memRegion (sp' + 176#64) 48 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words6_entails_memRegion48 (sp' + 176#64) ew0 ew1 ew2 ew3 ew4 ew5
  have hm120 :
      ((sp' + 312#64) ↦₆₄ errTag) ∗ ((sp' + 320#64) ↦₆₄ ew0) ∗ ((sp' + 328#64) ↦₆₄ ew1) ∗
      ((sp' + 336#64) ↦₆₄ ew2) ∗ ((sp' + 344#64) ↦₆₄ ew3) ∗ ((sp' + 352#64) ↦₆₄ ew4) ∗ ((sp' +
        360#64) ↦₆₄ ew5) ∗
      memRegion (sp' + 368#64) 64 ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words7_memRegion64_entails_memRegion120 (sp' + 312#64) errTag ew0 ew1 ew2 ew3 ew4 ew5
  have hcomb := sepConj_mono_right
    (P := ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
      A.pool lim st1 s2 ∗ stackAt sp' smallRootStack)
    (sepConj_mono herr_res (sepConj_mono hm48 hm120))
  refine SepWPp.mono_pre (P' :=
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim st1 s2 ∗ stackAt sp' smallRootStack) ∗
      (preKeyResultAt A.repAlloc x.sret x ∗ memRegion (sp' + 176#64) 48 ∗
        memRegion (sp' + 312#64) 120))
    (by
      refine Entails.trans ?_ hcomb
      rw [hstack]
      simp only [allocHookStack, smallRootStack, arm64_norm]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.frame_noPanic_pk
    (cleanup_554_placed_wp (st := st1) hkf hdealloc x.inner x.ikBytes x.bkBytes
      ⟨hsp2, hsp2_align, hinv2, htr2⟩
      hpc2 hrun2 hx23_2 hx26_2)
    fun sf Pf ⟨evs2, hevs2, hstf, hent⟩ =>
      ⟨rustDeallocEvents 1569 1 ++ evs2, (freeOnly_rustDeallocEvents 1569 1).append hevs2,
        hstf, ?_⟩
  rw [M.stepEvents_append]
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; sep_ac_rfl

/-! ## Cleanup Tail `+2416 .. +2420` → `+1284` and `post_seg4_ok_pack_placed_wp` -/

section OkPack

attribute [local arm64_norm, local wp_norm]
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

theorem cleanup_4a0_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {s0 s : State} {sp' msgCap msgPtr ikCap ikPtr bkCap bkPtr : BitVec 64}
    (msg ik bk : List (BitVec 8))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2416#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx26 : s.readReg64 .x26 = msgCap) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        vecU8Buf A.repAlloc msgCap msgPtr msg ∗ vecU8Buf A.repAlloc ikCap ikPtr ik ∗
        vecU8Buf A.repAlloc bkCap bkPtr bk ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  by_cases hcap : msgCap = 0#64
  · subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2616#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          vecU8Buf A.repAlloc ikCap ikPtr ik ∗ vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          A.pool lim st _ ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (cleanup_568_placed_wp hkf hdealloc ik bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, hevs, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; sep_ac_rfl
  · have hcap_beq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps_sync_111 ((blkPl_111).base + 2600#64)
    refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨inferInstance, fun hinv1 => ?_⟩
    refine SepWPp.let_state ?_; intro s_next
    have hst_next : PreKeyPostState Inv s0 sp' s_next :=
      PreKeyPostState.of_steps hinv1
        (by dsimp only [s_next]; tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by dsimp only [s_next]; simp [htr, arm64_norm])
    have hx23_next : s_next.readReg64 .x23 = ikCap := by
      dsimp only [s_next]; simp [hx23, arm64_norm]
    have hx26_next : s_next.readReg64 .x26 = msgCap := by
      dsimp only [s_next]; simp [hx26, arm64_norm]
    refine SepWPp.mono_pre
      (by dsimp only [s_next]; apply entails_of_eq; sep_ac_rfl)
      (cleanup_558_placed_wp (st := st) (bkCap := bkCap) (bkPtr := bkPtr)
        (msgPtr := msgPtr) (ikPtr := ikPtr) hkf hdealloc msg ik bk hcap hst_next
        (by simp_all [s_next, arm64_norm]) (by simp_all [s_next, arm64_norm])
        hx23_next hx26_next)

set_option maxHeartbeats 800000 in
theorem post_seg4_ok_pack_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' serBoxPtr kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64} {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ b : BitVec 64, (b ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (b ↦₆₄ rk0) ∗ ((b + 8#64) ↦₆₄ rk1) ∗ ((b + 16#64) ↦₆₄ rk2) ∗ ((b + 24#64) ↦₆₄ rk3))
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hser : serBoxPtr ≠ 0#64)
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serBoxPtr)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx27 : s.readReg64 .x27 = msgG.pqCap)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
        msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1 ∗
        boxU8Buf A.repAlloc serBoxPtr x.bytes ∗ boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A.repAlloc x.sret x ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hser_beq : (serBoxPtr == 0#64) = false := beq_eq_false_iff_ne.mpr hser
  rw [memRegion248_sret_split x.sret]
  simp only [sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_left (memRegion32_entails_pkLayoutAt (x.sret + 168#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_pre fun c0 => SepWPp.exists_pre fun c1 =>
    SepWPp.exists_pre fun c2 => SepWPp.exists_pre fun c3 =>
    SepWPp.exists_pre fun c4 => SepWPp.exists_pre fun c5 =>
    SepWPp.exists_pre fun c6 => SepWPp.exists_pre fun c7 =>
    SepWPp.exists_pre fun c8 => SepWPp.exists_pre fun cw9 =>
    SepWPp.exists_pre fun cw13 => SepWPp.exists_pre fun cw15 =>
    SepWPp.exists_pre fun cw23 => SepWPp.exists_pre fun cb31 => ?_
  rw [memRegion120_words15 x.sret,
      memRegion48_mid_eq (x.sret + 120#64),
      memRegion48_tail_eq (x.sret + 200#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun b240 =>
    SepWPp.exists_pre fun u1 => SepWPp.exists_pre fun u0 =>
    SepWPp.exists_pre fun w224 => SepWPp.exists_pre fun w216 =>
    SepWPp.exists_pre fun w208 => SepWPp.exists_pre fun w200 =>
    SepWPp.exists_pre fun k160 =>
    SepWPp.exists_pre fun w152 => SepWPp.exists_pre fun w144 =>
    SepWPp.exists_pre fun w136 => SepWPp.exists_pre fun w128 =>
    SepWPp.exists_pre fun p1 => SepWPp.exists_pre fun p0 =>
    SepWPp.exists_pre fun s14 => SepWPp.exists_pre fun s13 =>
    SepWPp.exists_pre fun s12 => SepWPp.exists_pre fun s11 =>
    SepWPp.exists_pre fun s10 => SepWPp.exists_pre fun s9 =>
    SepWPp.exists_pre fun s8 => SepWPp.exists_pre fun s7 =>
    SepWPp.exists_pre fun s6 => SepWPp.exists_pre fun s5 =>
    SepWPp.exists_pre fun s4 => SepWPp.exists_pre fun s3 =>
    SepWPp.exists_pre fun s2 => SepWPp.exists_pre fun s1 =>
    SepWPp.exists_pre fun s0_w => ?_
  dsimp only [sevenBytesHeadAt, pkLayoutAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2244#64) ?_
  wp_steps_sync_111 ((blkPl_111).base + 2244#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  have h136_tail := fun R => sevenBytesHead_tail_assoc (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h136_tail
  rw [h136_tail]
  refine SepWPp.of_sepWP_pk hkf hinv1 (mid := (blkPl_111).base + 2268#64) ?_
  wp_steps_sync_111 ((blkPl_111).base + 2268#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv2 => ?_⟩
  rw [← h136_tail]
  have h168_tail := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 c4 c5 c6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_tail
  rw [h168_tail]
  dsimp only [pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := (blkPl_111).base + 2416#64) ?_
  wp_steps_sync_111 ((blkPl_111).base + 2416#64)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨⟨by simp_all [arm64_norm]⟩, fun hinv3 => ?_⟩
  refine SepWPp.let_state ?_; intro s_pack
  have h168_head := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_head
  rw [← h168_head]
  have hres := preKeyResultAt_ok_intro A.repAlloc x innerMsg hsig msgG serBoxPtr kyberBoxPtr
    rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56 ik0 ik1 ik2 ik3 opkVal
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23 hopk hpk hrk hik
  dsimp only [msgWords15At, pkLayoutAt, sevenBytesHeadAt, pkRestAt] at hres
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hres
  have hm112 :
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 176#64) 112 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words14_entails_memRegion112 (sp' + 176#64)
        msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  have hcomb := sepConj_mono_right
    (P := ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
      vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ A.pool lim st s_pack ∗ stackAt sp' smallRootStack)
    (sepConj_mono hres
      (sepConj_mono_right (P :=
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3)) hm112))
  refine SepWPp.mono_pre (P' :=
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗ vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗ A.pool lim st s_pack ∗ stackAt sp' smallRootStack) ∗
      (preKeyResultAt A.repAlloc x.sret x ∗
        (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
          ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3)) ∗
        memRegion (sp' + 176#64) 112))
    (by
      refine Entails.trans ?_ hcomb
      dsimp only [s_pack]
      rw [opkTag_mask64_truncate32 x]
      simp only [sepConj_assoc, arm64_norm]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.frame_noPanic_pk
    (cleanup_4a0_placed_wp (st := st) hkf hdealloc x.inner x.ikBytes x.bkBytes
      (PreKeyPostState.of_steps hinv3 (by dsimp only [s_pack]; tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by dsimp only [s_pack]; simp [htr, arm64_norm]))
      (by simp_all [s_pack, arm64_norm]) (by simp_all [s_pack, arm64_norm])
      (by simp_all [s_pack, arm64_norm]) (by simp_all [s_pack, arm64_norm]))
    fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, hevs, hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; sep_ac_rfl

end OkPack

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
