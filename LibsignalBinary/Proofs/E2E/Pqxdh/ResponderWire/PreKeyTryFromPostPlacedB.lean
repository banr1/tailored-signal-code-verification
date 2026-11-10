/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedA
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Relocatable `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Post-Loop Part B

Proves post-loop Segments 2, 3, 4-error, and 4-ok packing (`+1668 .. +2648` → `+1284`) for
Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

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

def PreKeyIntoBoxOk [LibsignalPlacement] (Inv : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 56)
    (withPreKeyInv Inv (intoBoxedSliceSpec A))

def PreKeySigTryFromOk [LibsignalPlacement] (Inv : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 85)
    (withPreKeyInv Inv (tryFromPlacedSpec A))

theorem ls_subroutine_ok_cro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcro0, _⟩ := extract_withLsCodeRoLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcro0.1 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-! ## Segment 2 (`+1668 .. +1788` → `+2096`) -/

theorem post_seg2_1b4_to_360_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hIntoBox : PreKeyIntoBoxOk Inv A H)
    {x : PreKeyTryFromArgs} {s0 s : State}
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
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
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
            memRegion (sp' + 312#64) 48 ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗ A.pool ∗
            stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hky_eq := cap_add1_eq_of_lt hky_lt
  have hstackBox := stackAt_sub_split sp' intoBoxedSliceStack smallRootStack (by decide) (by decide)
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
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  have h313_tail := sevenBytesHeadAt_eq_tailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w112) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesHeadAt (sp' + 136#64) c0 c1 c2 c3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesTailAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [← h313_tail]
      dsimp only [sevenBytesHeadAt, pkRestAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv1 (mid := (blkPl_111).base + 1704#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv2
  have h136_tail := sevenBytesHeadAt_eq_tailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6
  refine SepWPp.mono_pre (P' :=
      ((sp' + 12#64) ↦₃₂ w12) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' +
        72#64) ↦₆₄ 33#64) ∗ spUnused112 sp' ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b120) ∗ ((sp' + 128#64) ↦₃₂ w128) ∗ ((sp' +
        132#64) ↦₁₆ w132) ∗
      sevenBytesTailAt (sp' + 136#64) b0 b1 b2 b3 c4 c5 c6 ∗ ((sp' + 312#64) ↦₈ 0#8) ∗
      sevenBytesHeadAt (sp' + 313#64) b0 b1 b2 b3 b4 b5 b6 ∗ pkRestAt (sp' +
        313#64) b7 b8 w9 w13 w15 w23 b31 ∗
      memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
    (by
      rw [sevenBytesHeadAt_eq_tailAt (sp' + 313#64), ← h136_tail]
      dsimp only [sevenBytesTailAt, pkRestAt, sevenBytesHeadAt]
      apply entails_of_eq; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := (blkPl_111).base + 1768#64) ?_
  dsimp only [sevenBytesTailAt, pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv3
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
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h136_head]
      dsimp only [sevenBytesTailAt]
      refine Entails.trans ?_ (sepConj_mono_left hcollapse)
      dsimp only [sevenBytesHeadAt, pkRestAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w320 => SepWPp.exists_pre fun w328 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv3 (mid := lsmpl.base 56) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv4
  have hvec_ky : vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes =
      ((sp' + 312#64) ↦₆₄ kyberCap) ∗ ((sp' + 320#64) ↦₆₄ kyberPtr) ∗
      ((sp' + 328#64) ↦₆₄ 1569#64) ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes := by
    rw [vecU8At_eq_header_buf]
    dsimp only [vecHeader]
    simp only [PreKeyTryFromArgs.kyberBytes_length, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
  refine SepWPp.call_tryFrom_pk hkf (⟨sp' + 312#64, kyberCap, kyberPtr, x.kyberBytes⟩ : VecArg)
    hIntoBox
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hinv4
    (ret_pc := (blkPl_111).base + 1780#64) (by simp_all [arm64_norm]) (by simp [htr, arm64_norm])
    (T := vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗ A.pool ∗
      stackAt sp' intoBoxedSliceStack)
    (φ := sp' + 312#64 = sp' + 312#64) (by simp_all [intoBoxedSliceSpec, VecArg.at, arm64_norm])
    rfl
    (by rw [hvec_ky, hstackBox]; sep_focus)
    ?_
  intro s5 hpc5 hrun5 hsp5 hsp5_align hinv5 hcs5
  dsimp only [intoBoxedSliceSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx1_5, htr5⟩ => ?_
  simp only [PreKeyTryFromArgs.kyberBytes_length] at hx1_5
  rcases hcs5 with ⟨hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, _, hx26_5, hx27_5, _, hx29_5⟩
  have hsp5_eq : s5.sp = sp' := by tryFromPost_sp [hsp5, hsp_eq]
  refine SepWPp.of_sepWP_end_pk hkf hinv5 ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv6
  refine ⟨s5.readReg64 .x0, ⟨by simp [hsp5_eq, arm64_norm],
      by simpa [State.spAligned, arm64_norm] using hsp5_align,
      hinv6, by simp [htr5, htr, arm64_norm]⟩,
    by simp [hx29_5, hx29, arm64_norm],
    by simp [arm64_norm],
    by simp [hx27_5, hx27, arm64_norm],
    by simp [hx26_5, hx26, arm64_norm],
    by simp [arm64_norm],
    by simp [hx24_5, arm64_norm],
    by simp [hx23_5, hx23, arm64_norm],
    by simp [hx22_5, hx22, arm64_norm],
    by simp [hx21_5, hx21, arm64_norm],
    by simp [hx20_5, hx20, arm64_norm],
    by simp [hx19_5, hx19, arm64_norm], ?_⟩
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
        boxU8Buf A (s5.readReg64 .x0) x.kyberBytes ∗ A.pool ∗ stackAt sp' smallRootStack))
    (by
      simp only [hstackBox, hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left h48) ?_
  dsimp only [sevenBytesHeadAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply entails_of_eq; ac_rfl

/-! ## Segment 3 (`+2096 .. +2168`) -/

theorem post_seg3_360_to_3a8_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks} (hSigTryFrom : PreKeySigTryFromOk Inv A H)
    {x : PreKeyTryFromArgs} {s0 s : State} {sp' kyberBoxPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
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
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
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
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗ lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hcallIk := ls_subroutine_ok_pk_of_cl
    (callerProg := preKeyPlacedProg H) hcl_of_inv (identityKeyTryFromSlice_placed_ok H)
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
      (ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h48_split]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
              (vecU8Buf_to_slice_rest A ikCap ikPtr x.ikBytes)))))))))))) ?_
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 116) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  have hik_deser : PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩ := deserialize_djb_ok x.idPub
  have hik_len : (33#64 : BitVec 64).toNat = x.ikBytes.length := by simp
  refine SepWPp.call_noPanic_pk hkf (ikPtr, x.ikBytes, ⟨x.idPub⟩, sp' + 312#64) hcallIk
    (by simp_all [arm64_norm]; rfl) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp) hinv1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp_all [arm64_norm])
    (T := (ikPtr ↦ₛ x.ikBytes) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ (33#64 : BitVec 64).toNat = x.ikBytes.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ PublicKey.deserialize x.ikBytes = .ok ⟨x.idPub⟩)
    (by simp_all [identityKeyTryFromSliceOkPlacedSpec, arm64_norm])
    ⟨rfl, hik_len, rfl, hik_deser⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [identityKeyTryFromSliceOkPlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h27_2 : s2.readReg64 .x27 = x.regId.zeroExtend 64 := by simp [hx27_2, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) 33#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  have hrepack_ik := slice_rest_to_vecU8Buf A ikCap ikPtr x.ikBytes
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
      Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ (msgPtr ↦ₛ x.inner) ∗
        vecU8Rest A msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split, memRegion32_words4 (sp' + 144#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [hik (sp' + 320#64)]
      simp only [hstackIk, hsp_eq,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
      refine Entails.sepExists_elim fun w168 => Entails.sepExists_elim fun w160 =>
        Entails.sepExists_elim fun w152 => Entails.sepExists_elim fun w144 => ?_
      refine Entails.trans ?_ (Entails.sepExists_intro w144)
      refine Entails.trans ?_ (Entails.sepExists_intro w152)
      refine Entails.trans ?_ (Entails.sepExists_intro w160)
      refine Entails.trans ?_ (Entails.sepExists_intro w168)
      refine Entails.trans (Q := ((ikPtr ↦ₛ x.ikBytes) ∗ vecU8Rest A ikCap ikPtr x.ikBytes) ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
          (((sp' + 144#64) ↦₆₄ w144) ∗ ((sp' + 152#64) ↦₆₄ w152) ∗ ((sp' + 160#64) ↦₆₄ w160) ∗
          ((sp' + 168#64) ↦₆₄ w168) ∗
            ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' +
            52#64) ↦₃₂ x.regId) ∗
            ((sp' + 56#64) ↦₃₂ 33#32) ∗ ((sp' + 60#64) ↦₃₂ 0#32) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            ((sp' + 104#64) ↦₆₄ ikPtr) ∗
            ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦₆₄ ik0) ∗ ((sp' +
            328#64) ↦₆₄ ik1) ∗
            ((sp' + 336#64) ↦₆₄ ik2) ∗ ((sp' + 344#64) ↦₆₄ ik3) ∗ memRegion (sp' + 352#64) 8 ∗
            memRegion (sp' + 360#64) 72 ∗ lsLogOff ∗ A.pool ∗ (memRegion (sp' -
            BitVec.ofNat 64 smallRootStack) (smallRootStack - 96) ∗ stackAt sp' 96)))
        (by apply entails_of_eq; ac_rfl) ?_
      refine Entails.trans
        (sepConj_mono hrepack_ik (sepConj_mono_left (vecU8Buf_to_slice_rest A msgCap msgPtr
        x.inner))) ?_
      apply entails_of_eq; ac_rfl) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun w144 => SepWPp.exists_pre fun w152 =>
    SepWPp.exists_pre fun w160 => SepWPp.exists_pre fun w168 => ?_
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := lsmpl.base 85) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv3
  have h120 := words5_memRegion8_72_entails_120 sp' 0xfffffffffffffffe#64 ik0 ik1 ik2 ik3
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗ (msgPtr ↦ₛ x.inner) ∗ vecU8Rest A msgCap msgPtr x.inner ∗
      lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack ∗ ((sp' +
        32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
      ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗ ((sp' +
        60#64) ↦₃₂ 0#32) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes)
    (by
      refine Entails.trans ?_ (sepConj_mono_left h120)
      apply entails_of_eq; ac_rfl) ?_
  have hin_toNat : (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length :=
    Nat.mod_eq_of_lt (by omega)
  have hlog_eq : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  refine SepWPp.call_tryFrom_pk hkf (⟨msgPtr, x.inner, sp' + 312#64⟩ : TryFromGhost) hSigTryFrom
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simpa [State.spAligned, arm64_norm] using hsp2_align) hinv3
    (ret_pc := (blkPl_111).base + 2168#64) (by simp_all [arm64_norm]) (by simp [htr2, htr, arm64_norm])
    (T := (msgPtr ↦ₛ x.inner) ∗ memRegion (sp' + 312#64) 120 ∗ lsLogOff ∗
      stackAt sp' smallRootStack ∗ A.pool)
    (φ := msgPtr = msgPtr ∧
      (BitVec.ofNat 64 x.inner.length).toNat = x.inner.length ∧
      x.inner.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64)
    (by simp_all [tryFromPlacedSpec, arm64_norm])
    ⟨rfl, hin_toNat, hlt_in, rfl⟩ (by sep_focus)
    ?_
  intro s4 hpc4 hrun4 hsp4 hsp4_align hinv4 hcs4
  dsimp only [tryFromPlacedSpec]
  rw [hlog_eq, sepConj_assoc]
  refine SepWPp.pure_pre fun htr4 => ?_
  rcases hcs4 with ⟨hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
    hx29_4, _⟩
  have hsp4_eq : s4.sp = sp' := by tryFromPost_sp [hsp4, hsp2_eq]
  refine SepWPp.of_sepWP_end_pk hkf hinv4 ?_
  refine SepWP.done hpc4 hrun4 ?_
  intro hinv5
  refine ⟨⟨hsp4_eq, hsp4_align, hinv5, by simp [htr4, htr2, htr, arm64_norm]⟩,
    by simp [hx29_4, h29_2, arm64_norm],
    by simp [hx28_4, hx28_2, hx28, arm64_norm],
    by simp [hx27_4, h27_2, arm64_norm],
    by simp [hx26_4, hx26_2, hx26, arm64_norm],
    by simp [hx25_4, hx25_2, hx25, arm64_norm],
    by simp [hx24_4, h24_2, arm64_norm],
    by simp [hx23_4, hx23_2, hx23, arm64_norm],
    by simp [hx22_4, hx22_2, hx22, arm64_norm],
    by simp [hx21_4, hx21_2, hx21, arm64_norm],
    by simp [hx20_4, hx20_2, hx20, arm64_norm],
    by simp [hx19_4, hx19_2, hx19, arm64_norm], ?_⟩
  have hrepack_msg := slice_rest_to_vecU8Buf A msgCap msgPtr x.inner
  refine Entails.trans
    (Q := ((msgPtr ↦ₛ x.inner) ∗ vecU8Rest A msgCap msgPtr x.inner) ∗
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        lsLogOff ∗ stackAt sp' smallRootStack ∗ A.pool ∗ ((sp' +
        32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 60#64) ↦₃₂ 0#32) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' +
        152#64) ↦₆₄ ik1) ∗ ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes))
    (by
      simp only [hsp2_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; ac_rfl

/-! ## Segment 4 Error Path (`+2168 .. +2648` → `+1284`) -/

theorem post_seg4_err_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
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
        104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 176#64) 48 ∗ signalMessageResultAt A [] (sp' +
        312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion x.sret 248 ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗
        stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧ (Pf ⊢ preKeyResultAt A x.sret x ∗ ((sp' +
        80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 176#64) 48 ∗
          memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have h554 := @cleanup_554_placed_wp _ Inv hkf A H hdealloc s0
  have hstack := stackAt_sub_split sp' allocHookStack smallRootStack (by decide) (by decide)
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (boxU8Buf_kyber_dealloc A kyberBoxPtr x))))))))))) ?_
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hky_ne => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (speAt_tryFrom_words2 A (sp' + 320#64) hsig)))))))) ?_
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
  refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).ρ lsRustDeallocSym) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  refine SepWPp.call_noPanic_pk hkf (kyberBoxPtr, 1569, 1) hdealloc
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2596#64) (by simp_all [arm64_norm])
    (T := A.pool ∗ A.live kyberBoxPtr 1569 1 ∗ memRegion kyberBoxPtr 1569 ∗
      stackAt s.sp allocHookStack)
    (φ := kyberBoxPtr = kyberBoxPtr ∧ (1569#64 : BitVec 64).toNat = 1569 ∧
      (1#64 : BitVec 64).toNat = 1)
    (by simp_all [rustDeallocSpec, arm64_norm])
    ⟨rfl, rfl, rfl⟩
    (by rw [hstack, hsp_eq]; sep_focus)
    ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [rustDeallocSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun htr2 => ?_
  rcases hcs2 with ⟨_, _, _, _, hx23_2, _, _, hx26_2, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have h23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_2, hx23, arm64_norm]
  have h26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_2, hx26, arm64_norm]
  have herr_res := err_result_entails_preKeyResultAt A x hsig ew0 ew1 ew2 ew3 ew4 ew5 hpack
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
      Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (sepConj_mono herr_res (sepConj_mono hm48 hm120))
  refine SepWPp.mono_pre (P' :=
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' +
        104#64) ↦₆₄ ikPtr) ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗ (preKeyResultAt A x.sret x ∗ memRegion (sp' +
        176#64) 48 ∗
        memRegion (sp' + 312#64) 120))
    (by
      refine Entails.trans ?_ hcomb
      simp only [hstack, hsp_eq, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (h554 x.inner x.ikBytes x.bkBytes
      ⟨hsp2_eq, hsp2_align, hinv2, by simp [htr2, htr, arm64_norm]⟩
      hpc2 hrun2 h23_2 h26_2)
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl

/-! ## Cleanup Tail `+2416 .. +2420` → `+1284` and `post_seg4_ok_pack_placed_wp` -/

section OkPack

open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

attribute [local arm64_norm, local wp_norm]
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

theorem cleanup_4a0_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
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
        Wire.vecU8Buf A msgCap msgPtr msg ∗ Wire.vecU8Buf A ikCap ikPtr ik ∗
        Wire.vecU8Buf A bkCap bkPtr bk ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf => PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have h558 := @cleanup_558_placed_wp _ Inv hkf A H hdealloc s0
  have h568 := @cleanup_568_placed_wp _ Inv hkf A H hdealloc s0
  by_cases hcap : msgCap = 0#64
  · clear h558
    subst hcap
    rw [vecU8Buf_zero]
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_pre fun _ => ?_
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2616#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          Wire.vecU8Buf A ikCap ikPtr ik ∗ Wire.vecU8Buf A bkCap bkPtr bk ∗
          A.pool ∗ stackAt sp' smallRootStack) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr))
      (by apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (h568 ik bk
        (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
          (by simp [htr, arm64_norm]))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl
  · clear h568
    have hcap_beq : (msgCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine SepWPp.of_sepWP_pk hkf hinv (mid := (blkPl_111).base + 2600#64) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    intro hinv1
    exact h558 msg ik bk hcap
      (PreKeyPostState.of_steps hinv1 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])

set_option maxHeartbeats 800000 in
theorem post_seg4_ok_pack_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks} (hdealloc : PreKeyDeallocOk Inv A H)
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
        msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
        boxU8Buf A serBoxPtr x.bytes ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗
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
          memRegion (sp' + 176#64) 112 ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have h4a0 := @cleanup_4a0_placed_wp _ Inv hkf A H hdealloc s0
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
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  have h136_tail := fun R => sevenBytesHead_tail_assoc (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h136_tail
  rw [h136_tail]
  refine SepWPp.of_sepWP_pk hkf hinv1 (mid := (blkPl_111).base + 2268#64) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv2
  rw [← h136_tail]
  have h168_tail := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 c4 c5 c6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_tail
  rw [h168_tail]
  dsimp only [pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv2 (mid := (blkPl_111).base + 2416#64) ?_
  wp_steps
  refine @SepWP.done _ _ _ _ _ _ ⟨by simp_all [arm64_norm]⟩
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv3
  have h168_head := fun R => sevenBytesHead_tail_assoc (x.sret + 168#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_head
  rw [← h168_head]
  have hres := preKeyResultAt_ok_intro A x innerMsg hsig msgG serBoxPtr kyberBoxPtr
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
      Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
      Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗ stackAt sp' smallRootStack)
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
        Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      (preKeyResultAt A x.sret x ∗
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
      rw [opkTag_mask64_truncate32 x]
      simp only [sepConj_assoc, arm64_norm]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (h4a0 x.inner x.ikBytes x.bkBytes
      (PreKeyPostState.of_steps hinv3 (by tryFromPost_sp [hsp_eq]) hsp_eq hsp
        (by simp [htr, arm64_norm]))
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]))
    fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; ac_rfl

end OkPack

end CryptoVerification.E2E.Pqxdh.ResponderWire
