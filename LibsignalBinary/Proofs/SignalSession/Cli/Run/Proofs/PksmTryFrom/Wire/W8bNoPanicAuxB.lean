/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWPresence
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWPresencePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aPresenceBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxB

section ErrPresence

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA (PreKeyPresenceErrNoPanicWPlaced post_bk_some_to_57c_noPanic_placed_wpW post_ik_some_to_590_noPanic_placed_wpW post_msg_some_to_5a4_noPanic_placed_wpW preKeyNoPanicQp w8b_bind_frame_noPanic w8b_errTail_close_noPanic_placed w8b_frame_noPanic w8b_of_sepWP_end_noPanic_pk)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_16 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48 bv_add_neg_512 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_8 bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded post_memRegion48_split8 preKeyCalleeSavedAt preKeyPlacedProg)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp deallocSlot entails_of_eq optVecU8Buf optVecU8Buf_entails_deallocSlot pure_true_emp)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap speAt speWord)
open CryptoVerification.RustHeap (RustAlloc vecHeader)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (BkNoneTailMem BkNoneTailStatePlaced IkNoneTailStatePlaced MsgNoneTailStatePlaced PreKeyLoopExitStatePlaced PresenceErrTailStatePlaced SpkNoneTailStatePlaced WirePreKeyGhost optVecU8Buf_cap_add2_ne pksmErrE pksmParse_bkNone pksmParse_ikNone pksmParse_msgNone pksmParse_spkNone seg1SpillsAtW stackAt_preKeyTryFromSubStack_skipField vecU8Buf_cap_lt_len vecU8Buf_entails_deallocSlot w8bBkNoneRestPlaced w8bBkNone_placed_pack w8bBkSomePresRestPlaced w8bBkSomePres_placed_pack w8bBkSomePres_placed_pack_61c w8bBkSomePres_placed_pack_66c w8bErrW_exists_pre_frame w8bMemRegion248_eq_words2 w8bMemRegion296_split_16_96 w8bOptU32Cells w8b_memRegion296_split96_104 w8b_open_61c w8b_open_66c w8b_open_678 w8b_open_ik_none_placed w8b_open_ik_some_placed w8b_open_msg_none w8b_open_msg_some w8b_open_spk_none w8b_optU32At_entails wirePreKeyAt wirePreKeyOf)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWP SepWPp
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (w8bRetPost w8bRetPost_prepend PksmPostEnv pksmPostEnv_of_missing_freeOnly)

private abbrev ep_of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev ep_of_sepWP_end_pk :=
  @w8b_of_sepWP_end_noPanic_pk

private theorem ep_sepWPp_introState {prog : Program} {ret : BitVec 64} {s1 : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ s_mid, s_mid = s1 → SepWPp prog ret s_mid P Q Qp) :
    SepWPp prog ret s1 P Q Qp :=
  h s1 rfl

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

private theorem ep_post_bk_none_to_5e0_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1504#64) s
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s)
      (fun sf Pf =>
        BkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ BkNoneTailMem A.repAlloc sp' kyberCap kyberPtr kyberLen bkPtr bkLen
          ikCap ikPtr ikLen msgCap msgPtr msgLen
          regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨hregs, hsp, hcl, htr⟩
  have hsp_eq := hregs.sp; have h29 := hregs.x29; have h27 := hregs.x27
  have h22 := hregs.x22; have h21 := hregs.x21; have h20 := hregs.x20; have h19 := hregs.x19
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (optVecU8Buf_cap_add2_ne A.repAlloc kyberCap kyberPtr kyberLen kyberOpt))))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜(kyberCap + 2#64 != 0#64) = true⌝ ∗
      (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hky_ne => ?_
  dsimp only [vecHeader]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine ep_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps_sync_pool ((blkPl_111).base + 1504#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [h29, arm64_norm], by simp [arm64_norm], by simp [h27, arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [h22, arm64_norm], by simp [h21, arm64_norm], by simp [h20, arm64_norm],
    by simp [h19, arm64_norm]⟩, ?_⟩
  dsimp only [BkNoneTailMem, vecHeader]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; sep_ac_rfl

private theorem ep_post_ik_none_to_61c_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr msgCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1564#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s)
      (fun sf Pf =>
        IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 => ep_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps_sync_pool ((blkPl_111).base + 1564#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, by apply entails_of_eq; sep_ac_rfl⟩

private theorem ep_post_msg_none_to_66c_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap x24 : BitVec 64} {vb : BitVec 8}
    (hst : MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1644#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s)
      (fun sf Pf =>
        MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 => ep_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps_sync_pool ((blkPl_111).base + 1644#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, by apply entails_of_eq; sep_ac_rfl⟩

private theorem ep_post_spk_none_to_678_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    (hst : SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1656#64) s
      (memRegion (sp' + 312#64) 48 ∗ A.pool lim st s)
      (fun sf Pf =>
        SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        (Pf ⊢ ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40 ∗
          A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left (post_memRegion48_split8 (sp' + 312#64))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w312 => ep_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
  wp_steps_sync_pool ((blkPl_111).base + 1656#64)
  refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
    by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
    by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩, by apply entails_of_eq; sep_ac_rfl⟩

private theorem ep_post_bk_none_full_to_5e0_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 kyberCap kyberPtr kyberLen bkPtr bkLen
      ikCap ikPtr ikLen msgCap msgPtr msgLen w96 w104 : BitVec 64} {vb : BitVec 8}
    {regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32}
    {kyberOpt ikOpt msgOpt : Option (List (BitVec 8))}
    (hst : PreKeyLoopExitStatePlaced s0 sp' sret len ptr0 vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1504#64) s
      ((((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
          vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          optVecU8Buf A.repAlloc ikCap ikPtr ikLen ikOpt ∗
          optVecU8Buf A.repAlloc msgCap msgPtr msgLen msgOpt ∗
          A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        BkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap spkTag vb sf ∧
        (Pf ⊢ ∃∗ kyAct : Bool, ∃∗ ikAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := (((sp' + 96#64) ↦₆₄ w96) ∗ ((sp' + 104#64) ↦₆₄ w104) ∗
        vecHeader (sp' + 312#64) kyberCap kyberPtr kyberLen ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal) ∗
        A.pool lim st s) ∗
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        optVecU8Buf A.repAlloc ikCap ikPtr ikLen ikOpt ∗
        optVecU8Buf A.repAlloc msgCap msgPtr msgLen msgOpt ∗
        stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_frame_noPanic
    (ep_post_bk_none_to_5e0_noPanic_placed_wpW hst hpc hrun hx24)
    fun sf Pf ⟨hbst, hent⟩ => ⟨hbst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  dsimp only [BkNoneTailMem]
  have hky := optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen kyberOpt
  have hik := optVecU8Buf_entails_deallocSlot A.repAlloc ikCap ikPtr ikLen ikOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A.repAlloc msgCap msgPtr msgLen msgOpt
  refine Entails.trans (Q :=
      (∃∗ kyAct : Bool, deallocSlot A.repAlloc kyberCap kyberPtr kyAct) ∗
      (∃∗ ikAct : Bool, deallocSlot A.repAlloc ikCap ikPtr ikAct) ∗
      (∃∗ msgAct : Bool, deallocSlot A.repAlloc msgCap msgPtr msgAct) ∗
      ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
        vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
        vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
        vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
        vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
        ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
        ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
        ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
    ?_ ?_
  · refine Entails.trans (Q :=
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        optVecU8Buf A.repAlloc ikCap ikPtr ikLen ikOpt ∗
        optVecU8Buf A.repAlloc msgCap msgPtr msgLen msgOpt ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          vecHeader (sp' + 312#64) 0x8000000000000002#64 kyberPtr kyberLen ∗
          vecHeader (sp' + 336#64) noneCap bkPtr bkLen ∗
          vecHeader (sp' + 360#64) ikCap ikPtr ikLen ∗
          vecHeader (sp' + 384#64) msgCap msgPtr msgLen ∗
          ((sp' + 408#64) ↦₃₂ regTag) ∗ ((sp' + 412#64) ↦₃₂ regVal) ∗
          ((sp' + 416#64) ↦₃₂ opkTag) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ spkTag) ∗ ((sp' + 428#64) ↦₃₂ spkVal) ∗
          ((sp' + 432#64) ↦₃₂ kpkTag) ∗ ((sp' + 436#64) ↦₃₂ kpkVal)))
      (by apply entails_of_eq; sep_ac_rfl)
      (sepConj_mono hky (sepConj_mono hik (sepConj_mono_left hmsg)))
  · simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun msgAct =>
      Entails.sepExists_elim fun ikAct =>
      Entails.sepExists_elim fun kyAct => ?_
    refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
    refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
    refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
    apply entails_of_eq; sep_ac_rfl

private theorem ep_post_ik_none_full_to_61c_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 bkCap bkPtr kyberCap kyberPtr kyberLen
      msgCap msgPtr msgLen x24 : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {kyberOpt msgOpt : Option (List (BitVec 8))}
    (hst : IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1404#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1564#64) s
      (memRegion (sp' + 312#64) 48 ∗
        (CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A.repAlloc msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        IkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr msgCap x24 vb sf ∧
        bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ bkAct : Bool, ∃∗ kyAct : Bool, ∃∗ msgAct : Bool,
          deallocSlot A.repAlloc bkCap bkPtr bkAct ∗ (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (vecU8Buf_entails_deallocSlot A.repAlloc bkCap bkPtr bk))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜bkCap ≠ noneCap⌝ ∗
      ((memRegion (sp' + 312#64) 48 ∗ A.pool lim st s) ∗
        ((∃∗ bkAct : Bool, deallocSlot A.repAlloc bkCap bkPtr bkAct) ∗
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          optVecU8Buf A.repAlloc msgCap msgPtr msgLen msgOpt ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hbk_ne => ?_
  refine w8b_frame_noPanic
    (ep_post_ik_none_to_61c_noPanic_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hist, hent⟩ => ⟨hist, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen kyberOpt
  have hmsg := optVecU8Buf_entails_deallocSlot A.repAlloc msgCap msgPtr msgLen msgOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hky (sepConj_mono_left hmsg)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  apply entails_of_eq; sep_ac_rfl

private theorem ep_post_msg_none_full_to_66c_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 ikCap ikPtr bkCap bkPtr kyberCap kyberPtr kyberLen
      x24 : BitVec 64} {vb : BitVec 8}
    {ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb s)
    (hpc : s.pc = (blkPl_111).base + 1424#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1644#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        MsgNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap x24 vb sf ∧
        ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A.repAlloc ikCap ikPtr ik)
        (sepConj_mono_right (sepConj_mono_left
          (vecU8Buf_entails_deallocSlot A.repAlloc bkCap bkPtr bk))))))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((memRegion (sp' + 312#64) 48 ∗ A.pool lim st s) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ ikAct : Bool, deallocSlot A.repAlloc ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A.repAlloc bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hik_ne => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hbk_ne => ?_
  refine w8b_frame_noPanic
    (ep_post_msg_none_to_66c_noPanic_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hmst, hent⟩ => ⟨hmst, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left hky))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; sep_ac_rfl

private theorem ep_post_spk_none_full_to_678_noPanic_placed_wpW [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 w0 w1 msgCap msgPtr ikCap ikPtr bkCap bkPtr
      kyberCap kyberPtr kyberLen : BitVec 64} {vb : BitVec 8}
    {msg ik bk : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    (hst : SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1444#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1656#64) s
      (memRegion (sp' + 312#64) 48 ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        SpkNoneTailStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb sf ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          (sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          ((sp' + 312#64) ↦₆₄ 0x8000000000000002#64) ∗ memRegion (sp' + 320#64) 40))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_deallocSlot A.repAlloc msgCap msgPtr msg)
        (sepConj_mono_right (sepConj_mono (vecU8Buf_entails_deallocSlot A.repAlloc ikCap ikPtr ik)
          (sepConj_mono_right (sepConj_mono_left
            (vecU8Buf_entails_deallocSlot A.repAlloc bkCap bkPtr bk))))))))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((memRegion (sp' + 312#64) 48 ∗ A.pool lim st s) ∗
        ((sret ↦₆₄ w0) ∗ ((sret + 8#64) ↦₆₄ w1) ∗
          (∃∗ msgAct : Bool, deallocSlot A.repAlloc msgCap msgPtr msgAct) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A.repAlloc ikCap ikPtr ikAct) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          (∃∗ bkAct : Bool, deallocSlot A.repAlloc bkCap bkPtr bkAct) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hmsg_ne =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hik_ne =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hbk_ne => ?_
  refine w8b_frame_noPanic
    (ep_post_spk_none_to_678_noPanic_placed_wpW hst hpc hrun)
    fun sf Pf ⟨hsst, hent⟩ => ⟨hsst, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hky))))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun bkAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; sep_ac_rfl

private theorem ep_w8b_pl_optVecU8Buf_none (A : RustAlloc) (cap ptr len : BitVec 64) :
    optVecU8Buf A cap ptr len none = ⌜cap = noneCap⌝ := rfl

private theorem ep_w8b_pl_optVecU8At_none_entails (A : RustAlloc) (pin : VecPin) (slot : BitVec 64) :
    CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A pin slot none ⊢
      ∃∗ bkp : BitVec 64, ∃∗ bkl : BitVec 64, vecHeader slot noneCap bkp bkl := by
  refine Entails.trans (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A pin slot none) ?_
  refine Entails.sepExists_elim fun bkc => Entails.sepExists_elim fun bkp =>
    Entails.sepExists_elim fun bkl => ?_
  rw [ep_w8b_pl_optVecU8Buf_none, sepConj_comm]
  refine Entails.pure_left fun hbkc => ?_
  subst hbkc
  exact Entails.trans
    (Entails.sepExists_intro (P := fun bkl => vecHeader slot noneCap bkp bkl) bkl)
    (Entails.sepExists_intro (P := fun bkp => ∃∗ bkl, vecHeader slot noneCap bkp bkl) bkp)

private theorem ep_w8b_pl_wirePreKeyAt_bk_some_eq (A : RustAlloc) (g : WirePreKeyGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) {bk : List (BitVec 8)} (hbk : m.baseKey = some bk) :
    wirePreKeyAt A g a m =
      (CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.kyberCt a m.kyberCiphertext ∗
        (vecHeader (a + 0x18#64) g.baseKey.cap g.baseKey.ptr (BitVec.ofNat 64 bk.length) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A g.baseKey.cap g.baseKey.ptr bk) ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.identityKey (a + 0x30#64) m.identityKey ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optVecU8At A g.message (a + 0x48#64) m.message ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x60#64) m.registrationId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x68#64) m.preKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x70#64) m.signedPreKeyId ∗
        CryptoVerification.LibsignalTripleRatchet.Prost.optU32At (a + 0x78#64) m.kyberPreKeyId) := by
  unfold wirePreKeyAt
  rw [hbk]
  rfl

private theorem ep_freeOnlyEvs_append {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) :
    FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with h | h
  · exact h1 ev h
  · exact h2 ev h

private theorem ep_w8b_close_pack [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st' : M.σ} {sf s0 : State}
    {x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost} {P Mid : SepProp}
    (hpk : Mid ⊢ pksmErrE (A.atState lim st' sf) [] x.ret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt (s0.sp - 608#64) CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack ∗
      memRegion (s0.sp - 608#64) 296 ∗
      memRegion (s0.sp - 608#64 + 296#64) 152 ∗
      memRegion (s0.sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ (A.atState lim st' sf).pool)
    (hP : P ⊢ Mid) :
    P ⊢ pksmErrE A.repAlloc [] x.ret .invalidProtobufEncoding ∗ SepProp.emp ∗
      stackAt (s0.sp - 608#64) CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack ∗
      memRegion (s0.sp - 608#64) 296 ∗
      memRegion (s0.sp - 608#64 + 296#64) 152 ∗
      memRegion (s0.sp - 608#64 + 448#64) 64 ∗
      preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
      (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim st' sf := by
  refine Entails.trans hP (Entails.trans hpk ?_)
  simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, pksmErrE, speAt]
  exact Entails.refl _

theorem w8b_presenceErr_bk_none_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s : State) (vb : BitVec 8)
    (m : ProtoPreKeySignalMessage)
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hbkO : m.baseKey = none)
    (hst : PreKeyLoopExitStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr vb s)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running) (hx24 : s.readReg64 .x24 = 0#64) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (wirePreKeyOf A.repAlloc (s0.sp - 608#64 + 312#64) m ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗
        memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion x.ret 248 ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        A.pool lim st s ∗ stackAt (s0.sp - 608#64) CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp := by
  rw [w8bMemRegion248_eq_words2 x.ret, stackAt_preKeyTryFromSubStack_skipField]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (w8b_memRegion296_split96_104 (s0.sp - 608#64)))) ?_
  unfold wirePreKeyOf
  rw [sepExists_sepConj_left]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => ?_
  unfold wirePreKeyAt
  rw [hbkO]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w8 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w104 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w96 => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.kyberCt _ m.kyberCiphertext)
      (sepConj_mono (ep_w8b_pl_optVecU8At_none_entails A.repAlloc g.baseKey _) (sepConj_mono
        (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.identityKey _ m.identityKey)
        (sepConj_mono (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.message _ m.message)
          (sepConj_mono (w8b_optU32At_entails _ m.registrationId)
            (sepConj_mono (w8b_optU32At_entails _ m.preKeyId)
              (sepConj_mono (w8b_optU32At_entails _ m.signedPreKeyId)
                (sepConj_mono_left (w8b_optU32At_entails _ m.kyberPreKeyId))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pKpk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pSpk =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pOpk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pReg =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun mc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun mp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ml =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikl =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun bkp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun bkl =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kl => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      (((((s0.sp - 608#64 + 96#64) ↦₆₄ w96) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ w104) ∗
          vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
          optVecU8Buf A.repAlloc kc kp kl m.kyberCiphertext ∗
          vecHeader (s0.sp - 608#64 + 336#64) noneCap bkp bkl ∗
          vecHeader (s0.sp - 608#64 + 360#64) ikc ikp ikl ∗
          vecHeader (s0.sp - 608#64 + 384#64) mc mp ml ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ pSpk.1.1) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ pSpk.1.2) ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2)) ∗
        ((x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
          optVecU8Buf A.repAlloc ikc ikp ikl m.identityKey ∗
          optVecU8Buf A.repAlloc mc mp ml m.message ∗
          A.pool lim st s ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))) ∗
      (memRegion (s0.sp - 608#64) 96 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
          (CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic (ep_post_bk_none_full_to_5e0_noPanic_placed_wpW hst hpc hrun hx24) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hP1⟩
  obtain ⟨hpost1, _hx29, hx28, hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst1
  change s1.readReg64 .x27 = speWord 2 at hx27
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP1) ?_
  refine w8bErrW_exists_pre_frame fun kyAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun msgAct => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      deallocSlot A.repAlloc kc kp kyAct ∗ (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        deallocSlot A.repAlloc ikc ikp ikAct ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        deallocSlot A.repAlloc mc mp msgAct ∗ ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗
        A.pool lim st s1 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
        w8bBkNoneRestPlaced s0 (s0.sp - 608#64) x.ret x.ptr kp kl bkp bkl
          ikc ikp ikl mc mp ml pReg.1.1 pReg.1.2 pOpk.1.1 pOpk.1.2 pSpk.1.1 pSpk.1.2
          pKpk.1.1 pKpk.1.2 x.bytes)
    (by unfold w8bBkNoneRestPlaced; apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (ErrTailBWPlacedBudget.entry_5e0_placed_wpX hC kyAct ikAct msgAct hpost1 hpc1 hrun1 hx19 hx27 hx28 hx25 hx23 hx26) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', evs, hfree, hP2⟩
  have hpk := @w8bBkNone_placed_pack _ (A.atState lim (M.stepEvents evs st) s2) s0
    (s0.sp - 608#64) x.ret x.ptr kp kl bkp bkl ikc ikp ikl mc mp ml
    pReg.1.1 pReg.1.2 pOpk.1.1 pOpk.1.2 pSpk.1.1 pSpk.1.2 pKpk.1.1 pKpk.1.2 x.bytes
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (ep_w8b_close_pack hpk (Entails.trans hP2 (by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)))
    (w8b_errTail_close_noPanic_placed hparse hfree hst2 hpc2 hrun2)

theorem w8b_presenceErr_ik_none_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s1 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt msgOpt : Option (List (BitVec 8))) (bk : List (BitVec 8))
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hst1 : PresenceErrTailStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s1)
    (hpc1 : s1.pc = (blkPl_111).base + 1404#64)
    (hrun1 : s1.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s1
      ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        memRegion (s0.sp - 608#64 + 432#64) 8 ∗
        optVecU8Buf A.repAlloc kc kp kl kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s1 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (optVecU8Buf A.repAlloc ikc ikp ikl none ∗
        optVecU8Buf A.repAlloc mc mp ml msgOpt ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
          (CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp := by
  change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp _ _ _
    ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
        regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
      memRegion (s0.sp - 608#64 + 312#64) 48 ∗
      memRegion (s0.sp - 608#64 + 360#64) 72 ∗
      memRegion (s0.sp - 608#64 + 432#64) 8 ∗
      optVecU8Buf (A.atState lim st s1) kc kp kl kyberOpt ∗
      CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf (A.atState lim st s1) bkCap bkPtr bk ∗
      (A.atState lim st s1).pool ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
    (optVecU8Buf (A.atState lim st s1) ikc ikp ikl none ∗
      optVecU8Buf (A.atState lim st s1) mc mp ml msgOpt ∗ _)) _ _
  rw [ep_w8b_pl_optVecU8Buf_none, w8b_open_ik_none_placed]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hikc => ?_
  subst hikc
  refine w8b_bind_frame_noPanic (ep_post_ik_none_full_to_61c_noPanic_placed_wpW hst1 hpc1 hrun1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, hbk_ne, hP2⟩
  obtain ⟨hpost2, _hx29, hx28, hx27, hx26, hx25, _hx24, _hx23, _hx22, _hx21, _hx20, hx19⟩ := hst2
  change s2.readReg64 .x27 = speWord 2 at hx27
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP2) ?_
  refine w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct =>
    w8bErrW_exists_pre_frame fun msgAct => ?_
  rw [w8b_open_61c]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (ErrTailBWPlacedBudget.entry_61c_placed_wpX hC bkAct kyAct msgAct hpost2 hpc2 hrun2 hx19 hx27 hx28 hx25 hx26 hbk_ne) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, _hx19', evs, hfree, hP3⟩
  have hpk := @w8bBkSomePres_placed_pack_61c _ (A.atState lim (M.stepEvents evs st) s3) s0
    (s0.sp - 608#64) x.ret x.ptr ml kl ikl (BitVec.ofNat 64 bk.length) bkPtr bkCap mp ikp
    0x8000000000000002#64 regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (ep_w8b_close_pack hpk (Entails.trans hP3 (by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)))
    (w8b_errTail_close_noPanic_placed hparse hfree hst3 hpc3 hrun3)

theorem w8b_presenceErr_msg_none_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s2 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik : List (BitVec 8))
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hst2 : PresenceErrTailStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s2)
    (hpc2 : s2.pc = (blkPl_111).base + 1424#64)
    (hrun2 : s2.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s2
      ((memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        A.pool lim st s2 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikc ikp ik ∗
        optVecU8Buf A.repAlloc mc mp ml none ∗
        optVecU8Buf A.repAlloc kc kp kl kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRestPlaced s0 (s0.sp - 608#64) x.ret x.ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes))
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp := by
  rw [ep_w8b_pl_optVecU8Buf_none, w8b_open_msg_none]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hmc => ?_
  subst hmc
  refine w8b_bind_frame_noPanic (ep_post_msg_none_full_to_66c_noPanic_placed_wpW hst2 hpc2 hrun2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, hik_ne, hbk_ne, hP3⟩
  obtain ⟨hpost3, _hx29, hx28, hx27, _hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst3
  change s3.readReg64 .x27 = speWord 2 at hx27
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP3) ?_
  refine w8bErrW_exists_pre_frame fun ikAct => w8bErrW_exists_pre_frame fun bkAct =>
    w8bErrW_exists_pre_frame fun kyAct => ?_
  rw [w8b_open_66c]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (ErrTailBWPlacedBudget.entry_66c_placed_wpX hC ikAct bkAct kyAct hpost3 hpc3 hrun3 hx19 hx27 hx23 hx28 hx25
      hik_ne hbk_ne) ?_
  rintro s4 P4 hpc4 hrun4 ⟨hst4, _hx19', evs, hfree, hP4⟩
  have hpk := @w8bBkSomePres_placed_pack_66c _ (A.atState lim (M.stepEvents evs st) s4) s0
    (s0.sp - 608#64) x.ret x.ptr ml kl ikl (BitVec.ofNat 64 bk.length) bkPtr bkCap mp ikp
    0x8000000000000002#64 regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (ep_w8b_close_pack hpk (Entails.trans hP4 (by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)))
    (w8b_errTail_close_noPanic_placed hparse hfree hst4 hpc4 hrun4)

theorem w8b_presenceErr_spk_none_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s2 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt : Option (List (BitVec 8))) (bk ik msg : List (BitVec 8))
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hst2 : PresenceErrTailStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc ((0#32 : BitVec 32).zeroExtend 64) vb s2)
    (hpc2 : s2.pc = (blkPl_111).base + 1424#64)
    (hrun2 : s2.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s2
      ((memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        A.pool lim st s2 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikc ikp ik ∗
        optVecU8Buf A.repAlloc mc mp ml (some msg) ∗
        optVecU8Buf A.repAlloc kc kp kl kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        ((s0.sp - 608#64 + 96#64) ↦₆₄ mp) ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikp) ∗
        w8bBkSomePresRestPlaced s0 (s0.sp - 608#64) x.ret x.ptr ml kl ikl
          (BitVec.ofNat 64 bk.length) regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes))
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp := by
  have hmsg_buf : optVecU8Buf A.repAlloc mc mp ml (some msg) ⊢
      ⌜mc.toNat < 2 ^ 63⌝ ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc mc mp msg := by
    dsimp only [optVecU8Buf]
    refine Entails.pure_left fun _ => ?_
    refine Entails.trans (vecU8Buf_cap_lt_len A.repAlloc mc mp msg)
      (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
    rw [pure_true_emp hlt, emp_sepConj]; exact Entails.refl _
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmsg_buf))) ?_
  rw [w8b_open_msg_some]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hmsg_lt => ?_
  refine w8b_bind_frame_noPanic (post_msg_some_to_5a4_noPanic_placed_wpW hC hst2 hpc2 hrun2 hmsg_lt) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hst3, evs₁, hfree₁, hP3⟩
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post ?_
    (fun _ _ _ _ hq => w8bRetPost_prepend (fun _ hfree₂ => ep_freeOnlyEvs_append hfree₁ hfree₂) hq)
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP3) ?_
  rw [w8b_open_spk_none]
  refine w8b_bind_frame_noPanic (ep_post_spk_none_full_to_678_noPanic_placed_wpW hst3 hpc3 hrun3) ?_
  rintro s4 P4 hpc4 hrun4 ⟨hst4, hmsg_ne, hik_ne, hbk_ne, hP4⟩
  obtain ⟨hpost4, _hx29, hx28, hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩ := hst4
  change s4.readReg64 .x27 = speWord 2 at hx27
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP4) ?_
  refine w8bErrW_exists_pre_frame fun msgAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct => ?_
  rw [w8b_open_678]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (ErrTailBWPlacedBudget.entry_678_placed_wpX hC msgAct ikAct bkAct kyAct hpost4 hpc4 hrun4 hx19 hx27 hx26 hx23 hx28 hx25
      hmsg_ne hik_ne hbk_ne) ?_
  rintro s5 P5 hpc5 hrun5 ⟨hst5, _hx19', evs, hfree, hP5⟩
  have hpk := @w8bBkSomePres_placed_pack _ (A.atState lim (M.stepEvents evs (M.stepEvents evs₁ st)) s5) s0
    (s0.sp - 608#64) x.ret x.ptr ml kl ikl (BitVec.ofNat 64 bk.length) bkPtr bkCap mp ikp
    0x8000000000000002#64 regTag regVal opkTag opkVal spkVal kpkTag kpkVal x.bytes
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (ep_w8b_close_pack hpk (Entails.trans hP5 (by
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]; apply entails_of_eq; sep_ac_rfl)))
    (w8b_errTail_close_noPanic_placed hparse hfree hst5 hpc5 hrun5)

theorem w8b_presenceErr_after_57c_noPanic_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 s1 : State) (vb : BitVec 8)
    (bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml w0 w8 : BitVec 64)
    (regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal : BitVec 32)
    (kyberOpt ikOpt msgOpt : Option (List (BitVec 8))) (spkOpt : Option (BitVec 32))
    (bk : List (BitVec 8))
    (hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none)
    (hspkCells : w8bOptU32Cells spkOpt (spkTag, spkVal))
    (herr : ikOpt = none ∨ msgOpt = none ∨ spkOpt = none)
    (hst1 : PresenceErrTailStatePlaced s0 (s0.sp - 608#64) x.ret
      (BitVec.ofNat 64 x.bytes.length) x.ptr kc kp ikc mc (spkTag.zeroExtend 64) vb s1)
    (hpc1 : s1.pc = (blkPl_111).base + 1404#64)
    (hrun1 : s1.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s1
      ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        memRegion (s0.sp - 608#64 + 432#64) 8 ∗
        optVecU8Buf A.repAlloc kc kp kl kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
        A.pool lim st s1 ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (optVecU8Buf A.repAlloc ikc ikp ikl ikOpt ∗
        optVecU8Buf A.repAlloc mc mp ml msgOpt ∗
        (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
        memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
        memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        memRegion (x.ret + 16#64) 232 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
        memRegion (s0.sp - 608#64 - BitVec.ofNat 64 CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
          (CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (w8bRetPost A lim FreeOnlyEvs x st s0)
      preKeyNoPanicQp := by
  rcases hikO : ikOpt with _ | ik
  · exact w8b_presenceErr_ik_none_noPanic_placed hC x st s0 s1 vb bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml
      w0 w8 regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt msgOpt bk
      hparse hst1 hpc1 hrun1
  · have hik_buf : optVecU8Buf A.repAlloc ikc ikp ikl (some ik) ⊢
        ⌜ikc.toNat < 2 ^ 63⌝ ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikc ikp ik := by
      dsimp only [optVecU8Buf]
      refine Entails.pure_left fun _ => ?_
      refine Entails.trans (vecU8Buf_cap_lt_len A.repAlloc ikc ikp ik)
        (Entails.pure_left fun ⟨_, hlt, _⟩ => ?_)
      rw [pure_true_emp hlt, emp_sepConj]; exact Entails.refl _
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_right (sepConj_mono_left hik_buf)) ?_
    change CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp _ _ _
      ((seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kl ikp ikl mp ml
          regTag regVal opkTag opkVal spkVal kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 312#64) 48 ∗
        memRegion (s0.sp - 608#64 + 360#64) 72 ∗
        memRegion (s0.sp - 608#64 + 432#64) 8 ∗
        optVecU8Buf (A.atState lim st s1) kc kp kl kyberOpt ∗
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf (A.atState lim st s1) bkCap bkPtr bk ∗
        (A.atState lim st s1).pool ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      ((⌜ikc.toNat < 2 ^ 63⌝ ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf (A.atState lim st s1) ikc ikp ik) ∗
        optVecU8Buf (A.atState lim st s1) mc mp ml msgOpt ∗ _)) _ _
    rw [w8b_open_ik_some_placed]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hik_lt => ?_
    refine w8b_bind_frame_noPanic (post_ik_some_to_590_noPanic_placed_wpW hC hst1 hpc1 hrun1 hik_lt) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hst2, evs₁, hfree₁, hP2⟩
    refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post ?_
      (fun _ _ _ _ hq => w8bRetPost_prepend (fun _ hfree₂ => ep_freeOnlyEvs_append hfree₁ hfree₂) hq)
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP2) ?_
    rcases hmsgO : msgOpt with _ | msg
    · exact w8b_presenceErr_msg_none_noPanic_placed hC x (M.stepEvents evs₁ st) s0 s2 vb bkCap bkPtr kc kp kl ikc ikp ikl mc mp ml
        w0 w8 regTag regVal opkTag opkVal spkTag spkVal kpkTag kpkVal kyberOpt bk ik
        hparse hst2 hpc2 hrun2
    · have hspkO : spkOpt = none := by
        rcases herr with h | h | h
        · simp [hikO] at h
        · simp [hmsgO] at h
        · exact h
      subst hspkO
      have hspk0 : spkTag = 0#32 := hspkCells
      subst hspk0
      exact w8b_presenceErr_spk_none_noPanic_placed hC x (M.stepEvents evs₁ st) s0 s2 vb bkCap bkPtr kc kp kl ikc ikp ikl
        mc mp ml w0 w8 regTag regVal opkTag opkVal spkVal kpkTag kpkVal kyberOpt bk ik msg
        hparse hst2 hpc2 hrun2

theorem preKeyPresenceErrNoPanicW_placed_proof [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) :
    PreKeyPresenceErrNoPanicWPlaced M A lim H := by
  intro x st s0 s vb b1 bs1 m _hfit hcons _hv3 _hv4 _hlen hdec herr hst hpc hrun hx24
  have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none := by
    rw [hcons]
    rcases herr with h | h | h | h
    · exact pksmParse_bkNone hdec h
    · exact pksmParse_ikNone hdec h
    · exact pksmParse_msgNone hdec h
    · exact pksmParse_spkNone hdec h
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post ?_
    (fun _ _ _ _ hq => W8bAssemblyPlacedBudget.w8bRetPost_mono (fun _ h => pksmPostEnv_of_missing_freeOnly herr h) hq)
  rcases hbkO : m.baseKey with _ | bk
  · exact w8b_presenceErr_bk_none_noPanic_placed hC x st s0 s vb m hparse hbkO hst hpc hrun hx24
  · have herr' : m.identityKey = none ∨ m.message = none ∨ m.signedPreKeyId = none := by
      rcases herr with h | h
      · simp [hbkO] at h
      · exact h
    rw [w8bMemRegion296_split_16_96, w8bMemRegion248_eq_words2 x.ret,
      stackAt_preKeyTryFromSubStack_skipField]
    unfold wirePreKeyOf
    rw [sepExists_sepConj_left]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun g => ?_
    rw [ep_w8b_pl_wirePreKeyAt_bk_some_eq A.repAlloc g _ m hbkO]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w8 => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun w0 => ?_
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (sepConj_mono (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.kyberCt _ m.kyberCiphertext)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono
          (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.identityKey _ m.identityKey)
          (sepConj_mono (CryptoVerification.LibsignalTripleRatchet.Wire.optVecU8At_entails_header_buf A.repAlloc g.message _ m.message)
            (sepConj_mono (w8b_optU32At_entails _ m.registrationId)
              (sepConj_mono (w8b_optU32At_entails _ m.preKeyId)
                (sepConj_mono (w8b_optU32At_entails _ m.signedPreKeyId)
                  (sepConj_mono_left (w8b_optU32At_entails _ m.kyberPreKeyId)))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pKpk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pSpk =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pOpk => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun pReg =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun mc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun mp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ml =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikl =>
      CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kc => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kp => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun kl => ?_
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
        (memRegion (s0.sp - 608#64 + 16#64) 96 ∗
          vecHeader (s0.sp - 608#64 + 312#64) kc kp kl ∗
          optVecU8Buf A.repAlloc kc kp kl m.kyberCiphertext ∗
          vecHeader (s0.sp - 608#64 + 336#64) g.baseKey.cap g.baseKey.ptr
            (BitVec.ofNat 64 bk.length) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc g.baseKey.cap g.baseKey.ptr bk ∗
          vecHeader (s0.sp - 608#64 + 360#64) ikc ikp ikl ∗
          vecHeader (s0.sp - 608#64 + 384#64) mc mp ml ∗
          ((s0.sp - 608#64 + 408#64) ↦₃₂ pReg.1.1) ∗ ((s0.sp - 608#64 + 412#64) ↦₃₂ pReg.1.2) ∗
          ((s0.sp - 608#64 + 416#64) ↦₃₂ pOpk.1.1) ∗ ((s0.sp - 608#64 + 420#64) ↦₃₂ pOpk.1.2) ∗
          ((s0.sp - 608#64 + 424#64) ↦₃₂ pSpk.1.1) ∗ ((s0.sp - 608#64 + 428#64) ↦₃₂ pSpk.1.2) ∗
          ((s0.sp - 608#64 + 432#64) ↦₃₂ pKpk.1.1) ∗ ((s0.sp - 608#64 + 436#64) ↦₃₂ pKpk.1.2) ∗
          A.pool lim st s ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
        (optVecU8Buf A.repAlloc ikc ikp ikl m.identityKey ∗
          optVecU8Buf A.repAlloc mc mp ml m.message ∗
          (x.ret ↦₆₄ w0) ∗ ((x.ret + 8#64) ↦₆₄ w8) ∗
          memRegion (s0.sp - 608#64) 16 ∗ memRegion (s0.sp - 608#64 + 112#64) 184 ∗
          memRegion (s0.sp - 608#64 + 296#64) 16 ∗ memRegion (s0.sp - 608#64 + 440#64) 8 ∗
          memRegion (s0.sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
          memRegion (x.ret + 16#64) 232 ∗
          (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
          memRegion (s0.sp - 608#64 - BitVec.ofNat 64 CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack)
            (CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack - CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (by apply entails_of_eq; sep_ac_rfl) ?_
    refine w8b_bind_frame_noPanic (post_bk_some_to_57c_noPanic_placed_wpW hC hst hpc hrun hx24) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hst1, _, _, evs₁, hfree₁, hP1⟩
    refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
      (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP1)
        (w8b_presenceErr_after_57c_noPanic_placed hC x (M.stepEvents evs₁ st) s0 s1 vb g.baseKey.cap
          g.baseKey.ptr kc kp kl ikc ikp ikl mc mp ml w0 w8
          pReg.1.1 pReg.1.2 pOpk.1.1 pOpk.1.2 pSpk.1.1 pSpk.1.2 pKpk.1.1 pKpk.1.2
          m.kyberCiphertext m.identityKey m.message m.signedPreKeyId bk hparse pSpk.2 herr'
          hst1 hpc1 hrun1)) ?_
    intro sf Pf _ _ hq
    exact w8bRetPost_prepend (fun _ hfree₂ => ep_freeOnlyEvs_append hfree₁ hfree₂) hq

end ErrPresence

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxB
