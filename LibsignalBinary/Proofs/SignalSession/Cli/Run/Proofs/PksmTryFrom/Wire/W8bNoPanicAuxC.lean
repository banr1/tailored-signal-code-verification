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
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWBaseKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWBaseKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWSharedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5aBaseKeyWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyber
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bKyberPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlacedBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyber
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bErrWKyberPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKyberWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKey
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bIdentKeyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKeyWPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
meta import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostRkSome
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCleanup
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-!
# Panic-Free Budget-Threaded `base_key`, Kyber, and `identity_key` Continuations

Proves the budget-pool panic-free `base_key` error (`+0x5b4 → +0x7a8 → ret`), Kyber
`Ok` / `Err` (`+0x684 → +0x830` / `+0xa24 → ret`), and `identity_key` `Ok`
(`+0x830 → +0x864`) continuations over `RustCliAllocBudget M` on `preKeyPlacedProg H`.
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxC

section ErrBaseKey

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA (PreKeyBaseKeyErrNoPanicWPlaced preKeyNoPanicQp w8b_bind_frame_noPanic w8b_errTail_close_noPanic_placed w8b_of_sepWP_end_noPanic_pk)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (InvalidMessageReason SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_add_neg_104 bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_16 bv_add_neg_160 bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191 bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40 bv_add_neg_48 bv_add_neg_512 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72 bv_add_neg_8 bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded preKeyCalleeSavedAt preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (SepWPp deallocSlot deserializeResult33At entails_of_eq memRegion33_of_err_badKeyLength memRegion33_of_err_badKeyType memRegion33_of_err_base optVecU8Buf optVecU8Buf_entails_deallocSlot pure_true_emp slice_rest_entails_vecU8Buf vecU8Buf_entails_slice_rest)
open CryptoVerification.LibsignalTripleRatchetRepr (invalidMessageStrAt noneCap speAt speWord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (DeserErrTailStateEPlaced PresenceOkStatePlaced pksmErrE pksmParse_bkErr seg1SpillsAtW speWordsOf w8bBkErrRest w8bBkErr_placed_pack w8bErrW_exists_pre_frame w8bPostLoopFramePlaced w8bXokPost)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWP SepWPp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget (entry_7a8_placed_wpE)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (pksmFrom5b4Env_of_err_freeOnly)

private abbrev ebk_of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev ebk_of_sepWP_end_pk :=
  @w8b_of_sepWP_end_noPanic_pk

private theorem ebk_sepWPp_introState {prog : Program} {ret : BitVec 64} {s1 : State}
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

private theorem ebk_post_deser_bk_err_to_7a8_noPanic_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1472#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      (deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
        memRegion (sp' + 345#64) 15 ∗ A.pool lim st s)
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  rw [herr]
  cases e with
  | noKeyTypeIdentifier =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine ebk_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps_sync_pool ((blkPl_111).base + 1960#64)
    refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_base (sp' + 312#64) 0#8
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; sep_ac_rfl) (sepConj_mono_left h33)
  | badKeyType t =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine ebk_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps_sync_pool ((blkPl_111).base + 1960#64)
    refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyType (sp' + 312#64) t
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; sep_ac_rfl) (sepConj_mono_left h33)
  | badKeyLength n =>
    dsimp only [deserializeResult33At]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine ebk_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl ?_
    wp_steps_sync_pool ((blkPl_111).base + 1960#64)
    refine CryptoVerification.E2E.Pqxdh.ResponderWire.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
    refine ⟨⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
        by simp [htr, arm64_norm]⟩,
      by simp [hx29, arm64_norm], by simp [hx28, arm64_norm], by simp [hx27, arm64_norm],
      by simp [hx26, arm64_norm], by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
      by simp [hx23, arm64_norm], by simp [hx22, arm64_norm], by simp [hx21, arm64_norm],
      by simp [hx20, arm64_norm], by simp [hx19, arm64_norm]⟩,
      by simp [speWordsOf, speWord, arm64_norm]; bv_bits⟩, ?_⟩
    have h33 := memRegion33_of_err_badKeyLength (sp' + 312#64) n
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h33
    exact Entails.trans (by apply entails_of_eq; sep_ac_rfl) (sepConj_mono_left h33)
  | _ =>
    dsimp only [deserializeResult33At]
    exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hfalse => False.elim hfalse

private theorem ebk_post_deser_bk_err_full_to_7a8_noPanic_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr bkCap bkPtr ikCap msgCap : BitVec 64} {vb : BitVec 8}
    {bk : List (BitVec 8)} {e : SignalProtocolError}
    (herr : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      (((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
        A.pool lim st s)
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (Pf ⊢ ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗ A.pool lim st sf))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (W8bNoPanicAuxA.post_deser_bk_call_noPanic_placed_wpW hC bk hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hent1⟩
  let restF := ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' := (deserializeResult33At (sp' + 312#64) (CryptoGames.LibsignalSession.PublicKey.deserialize bk) ∗
      memRegion (sp' + 345#64) 15 ∗ A.pool lim st s1) ∗ restF)
    (Entails.trans hent1 (by dsimp only [restF]; apply entails_of_eq; sep_ac_rfl)) ?_
  refine W8bNoPanicAuxA.w8b_frame_noPanic
    (ebk_post_deser_bk_err_to_7a8_noPanic_placed_wpE herr hst1 hpc1 hrun1)
    fun sf Pf ⟨hdst, hent2⟩ => ⟨hdst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent2) ?_
  dsimp only [restF]; apply entails_of_eq; sep_ac_rfl

private theorem ebk_w5a_pl_vec_ne_noneCap (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A cap ptr bs ⊢ ⌜cap ≠ noneCap⌝ ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A cap ptr bs := by
  refine Entails.trans (vecU8Buf_entails_slice_rest A cap ptr bs)
    (Entails.pure_left fun ⟨_hle, hlt, _hptr⟩ => ?_)
  have hne : cap ≠ noneCap := by rintro rfl; revert hlt; decide
  rw [pure_true_emp hne, emp_sepConj]
  exact slice_rest_entails_vecU8Buf A cap ptr bs

private theorem ebk_w5a_pl_vec_entails_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A cap ptr bs ⊢ ∃∗ active : Bool, deallocSlot A cap ptr active := by
  refine Entails.trans ?_
    (optVecU8Buf_entails_deallocSlot A cap ptr (BitVec.ofNat 64 bs.length) (some bs))
  dsimp only [optVecU8Buf]
  rw [pure_true_emp rfl, emp_sepConj]
  exact Entails.refl _

private theorem ebk_w5a_pl_vec_ne_and_deallocSlot (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A cap ptr bs ⊢
      ⌜cap ≠ noneCap⌝ ∗ ∃∗ active : Bool, deallocSlot A cap ptr active :=
  Entails.trans (ebk_w5a_pl_vec_ne_noneCap A cap ptr bs)
    (sepConj_mono_right (ebk_w5a_pl_vec_entails_deallocSlot A cap ptr bs))

private theorem ebk_post_deser_bk_err_dealloc_to_7a8_noPanic_placed_wpE [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen
      bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64} {vb : BitVec 8}
    {bk ik msg : List (BitVec 8)} {kyberOpt : Option (List (BitVec 8))}
    {e : SignalProtocolError}
    (herr : CryptoGames.LibsignalSession.PublicKey.deserialize bk = .error e)
    (hst : PresenceOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb s)
    (hpc : s.pc = (blkPl_111).base + 1460#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1960#64) s
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff) ∗
        (memRegion sret 248 ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        DeserErrTailStateEPlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb e sf ∧
        (∃ x8v x9v x10v : BitVec 64,
          sf.readReg64 .x8 = x8v ∧ sf.readReg64 .x9 = x9v ∧ sf.readReg64 .x10 = x10v ∧
          speWordsOf e x9v x8v x10v) ∧
        msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap ∧
        (Pf ⊢ ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool, ∃∗ kyAct : Bool,
          memRegion sret 248 ∗
          deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          deallocSlot A.repAlloc kyberCap kyberPtr kyAct ∗
          A.pool lim st sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
          ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          memRegion (sp' + 312#64) 33 ∗ memRegion (sp' + 345#64) 15 ∗ lsLogOff))
      preKeyNoPanicQp := by
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (ebk_w5a_pl_vec_ne_noneCap A.repAlloc bkCap bkPtr bk)))))
      (sepConj_mono_right
        (sepConj_mono (ebk_w5a_pl_vec_ne_and_deallocSlot A.repAlloc msgCap msgPtr msg)
          (sepConj_mono_right (sepConj_mono_left
            (ebk_w5a_pl_vec_ne_and_deallocSlot A.repAlloc ikCap ikPtr ik)))))) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ⌜msgCap ≠ noneCap⌝ ∗ ⌜ikCap ≠ noneCap⌝ ∗ ⌜bkCap ≠ noneCap⌝ ∗
      ((((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (sp' + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗ lsLogOff ∗
          A.pool lim st s) ∗
        (memRegion sret 248 ∗
          (∃∗ msgAct : Bool, deallocSlot A.repAlloc msgCap msgPtr msgAct) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗
          (∃∗ ikAct : Bool, deallocSlot A.repAlloc ikCap ikPtr ikAct) ∗
          ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hmsg_ne =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hik_ne =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hbk_ne => ?_
  refine W8bNoPanicAuxA.w8b_frame_noPanic
    (ebk_post_deser_bk_err_full_to_7a8_noPanic_placed_wpE hC herr hst hpc hrun)
    fun sf Pf ⟨hdstE, hent⟩ =>
      ⟨hdstE, ⟨_, _, _, rfl, rfl, rfl, hdstE.2⟩, hmsg_ne, hik_ne, hbk_ne, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  have hky := optVecU8Buf_entails_deallocSlot A.repAlloc kyberCap kyberPtr kyberLen kyberOpt
  refine Entails.trans
    (sepConj_mono
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (ebk_w5a_pl_vec_entails_deallocSlot A.repAlloc bkCap bkPtr bk))))))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left hky)))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun kyAct =>
    Entails.sepExists_elim fun ikAct =>
    Entails.sepExists_elim fun msgAct =>
    Entails.sepExists_elim fun bkAct => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro msgAct)
  refine Entails.trans ?_ (Entails.sepExists_intro ikAct)
  refine Entails.trans ?_ (Entails.sepExists_intro bkAct)
  refine Entails.trans ?_ (Entails.sepExists_intro kyAct)
  apply entails_of_eq; sep_ac_rfl

private theorem ebk_vecU8_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8 (A.atState lim st s) v bs = CryptoVerification.RustHeap.vecU8 A.repAlloc v bs := by
  simp only [CryptoVerification.RustHeap.vecU8, CryptoVerification.RustHeap.vecU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]

private theorem ebk_invalidMessageStrAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt (A.atState lim st s) a r = invalidMessageStrAt A.repAlloc a r := by
  cases r <;> simp only [invalidMessageStrAt, ebk_vecU8_atState_eq]

private theorem ebk_pksmErrE_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (sret : BitVec 64) (e : SignalProtocolError) :
    pksmErrE (A.atState lim st s) fn sret e = pksmErrE A.repAlloc fn sret e := by
  cases e <;> simp only [pksmErrE, speAt, ebk_vecU8_atState_eq, ebk_invalidMessageStrAt_atState_eq]

theorem preKeyBaseKeyErrNoPanicW_placed_proof [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H) :
    PreKeyBaseKeyErrNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId e bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal _hfit hcons _hv3 _hv4 _hlen hdec
    hbkO _hikO _hmsgO _hspkO _hreg _hopk _hkpk hd hst _hbkC _hikC _hmsgC hpc hrun
  have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none := hcons ▸ pksmParse_bkErr hdec hbkO hd
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ((((s0.sp - 608#64 + 72#64) ↦₆₄ BitVec.ofNat 64 bk.length) ∗
          ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗
          memRegion (s0.sp - 608#64 + 312#64) 48 ∗ CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc bkCap bkPtr bk ∗
          lsLogOff) ∗
        (memRegion x.ret 248 ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗ ((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗
          CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc ikCap ikPtr ik ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikPtr) ∗
          ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
          optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
          A.pool lim st sf ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))) ∗
      w8bBkErrRest s0 (s0.sp - 608#64) x.ptr (BitVec.ofNat 64 msg.length) kyberLen
        (BitVec.ofNat 64 ik.length) regTag regVal opkTag opkVal spkId kpkTag kpkVal x.bytes)
    (by
      unfold w8bXokPost w8bPostLoopFramePlaced seg1SpillsAtW w8bBkErrRest
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc, CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, optVecU8Buf]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic
    (ebk_post_deser_bk_err_dealloc_to_7a8_noPanic_placed_wpE hC hd hst hpc hrun) ?_
  rintro s1 P1 hpc1 hrun1
    ⟨⟨⟨hpost1, _hx29, hx28, _hx27, hx26, hx25, _hx24, hx23, _hx22, _hx21, _hx20, hx19⟩, _⟩,
      ⟨x8v, x9v, x10v, hx8, hx9, hx10, hwords⟩, hmsgNe, hikNe, hbkNe, hP1⟩
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hP1) ?_
  refine w8bErrW_exists_pre_frame fun msgAct => w8bErrW_exists_pre_frame fun ikAct =>
    w8bErrW_exists_pre_frame fun bkAct => w8bErrW_exists_pre_frame fun kyAct => ?_
  refine w8b_bind_frame_noPanic
    (entry_7a8_placed_wpE hC msgAct ikAct bkAct kyAct hpost1 hpc1 hrun1 hx19 hx8 hx9 hx10 hwords
      hx26 hx23 hx28 hx25 hmsgNe hikNe hbkNe) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hst2, _hx19', evs, hfree, hP2⟩
  have hpk := @w8bBkErr_placed_pack _ (A.atState lim (M.stepEvents evs st) s2) s0
    (s0.sp - 608#64) x.ret x.ptr (BitVec.ofNat 64 msg.length) kyberLen
    (BitVec.ofNat 64 ik.length) msgPtr ikPtr bkPtr bkCap (BitVec.ofNat 64 bk.length)
    regTag regVal opkTag opkVal spkId kpkTag kpkVal e x.bytes
  have hpack' : P2 ∗ w8bBkErrRest s0 (s0.sp - 608#64) x.ptr (BitVec.ofNat 64 msg.length) kyberLen
      (BitVec.ofNat 64 ik.length) regTag regVal opkTag opkVal spkId kpkTag kpkVal x.bytes ⊢
      pksmErrE A.repAlloc [] x.ret e ∗ SepProp.emp ∗
        stackAt (s0.sp - 608#64) CryptoVerification.E2E.Pqxdh.ResponderWire.preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents evs st) s2 := by
    refine Entails.trans (sepConj_mono_left hP2) (Entails.trans ?_ (Entails.trans hpk ?_))
    · rw [ebk_pksmErrE_atState_eq]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
      apply entails_of_eq; sep_ac_rfl
    · rw [ebk_pksmErrE_atState_eq]
      exact Entails.refl _
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hpack'
    (w8b_errTail_close_noPanic_placed hparse (pksmFrom5b4Env_of_err_freeOnly hd hfree) hst2 hpc2 hrun2)

end ErrBaseKey

section Kyber

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA (PreKey684OkNoPanicWPlaced preKeyNoPanicQp w8b_bind_frame_noPanic)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet.Wire (entails_of_eq optVecU8Buf pkBytesOf pure_true_emp)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (BaseKeyOkStatePlaced KyberOkStatePlaced seg1SpillsAtW vecU8Buf_cap_lt_len w8bOptU32Cells w8bRowKFrame w8bRowKPostPlaced w8bRowYFramePlaced w8bRowYPost w8b_kyber_dispatch w8b_memRegion16_split w8b_memRegion184_split)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W5bKybercWPlacedBudget (w5b_kyber_ok_placed_wpW)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (w8bRetPost w8bRetPost_prepend PksmFrom684Env PksmFrom830Env fitsEnv_pksmFrom684_ok_box fitsEnv_pksmFrom684_ok_step pksmFrom684Env_of_ok)

def PreKey830OkNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    FitsEnv M lim st (PksmFrom830Env x.bytes ik msg) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    KyberOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 2096#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowYPost (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr kyberLen ikPtr msgPtr
          kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal
          p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb
          m.kyberPreKeyId m.kyberCiphertext ik msg ∗
        w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr
          msgCap msgPtr bk ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom830Env x.bytes ik msg) x st s0)
      preKeyNoPanicQp

def PreKeyKyberErrNoPanicWPlaced [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State)
    (vb b1 : BitVec 8) (bs1 : List (BitVec 8))
    (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8)) (spkId : BitVec 32)
    (pk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap kyberPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32),
    FitsEnv M lim st (PksmFrom684Env vb x.bytes ik msg m.kyberPreKeyId m.kyberCiphertext) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome != m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ 0x40 ≤ vb.toNat)) →
    BaseKeyOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberCap kyberPtr ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 1668#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowKPostPlaced (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr bk ∗
        w8bRowKFrame (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap kyberCap kyberPtr
          kyberLen ikCap ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkTag kpkVal
          m.kyberCiphertext ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom684Env vb x.bytes ik msg m.kyberPreKeyId m.kyberCiphertext)
        x st s0)
      preKeyNoPanicQp

private theorem ky_kyber_ok_cond {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {vb : BitVec 8}
    (hok : (kpkOpt.isSome && kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ vb.toNat < 0x40)) :
    (kpkOpt.isSome == kyberOpt.isSome) = true ∧
      (kpkOpt = none → kyberOpt = none → vb.toNat < 0x40) := by
  rcases hok with hboth | ⟨rfl, rfl, hlt⟩
  · refine ⟨?_, fun hk _ => by simp [hk] at hboth⟩
    cases kpkOpt <;> cases kyberOpt <;> simp at hboth ⊢
  · exact ⟨rfl, fun _ _ => hlt⟩

private theorem ky_optVecU8Buf_cap_bnd (A : RustAlloc) (cap ptr len : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8Buf A cap ptr len opt ⊢
      ⌜∀ ct, opt = some ct → ct.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗
        optVecU8Buf A cap ptr len opt := by
  cases opt with
  | none =>
    have hp : ∀ ct, (none : Option (List (BitVec 8))) = some ct →
        ct.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := fun _ h => nomatch h
    rw [pure_true_emp hp, emp_sepConj]; exact Entails.refl _
  | some ct =>
    dsimp only [optVecU8Buf]
    refine Entails.pure_left fun hkl => ?_
    refine Entails.trans (vecU8Buf_cap_lt_len A cap ptr ct)
      (Entails.pure_left fun ⟨hle, hlt, _⟩ => ?_)
    have hp : ∀ ct', some ct = some ct' →
        ct'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 := by
      rintro _ ⟨rfl⟩; exact ⟨hle, hlt⟩
    rw [pure_true_emp hp, emp_sepConj, pure_true_emp hkl, emp_sepConj]
    exact Entails.refl _

theorem preKey684OkNoPanicW_placed_of_830 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    (hErr : PreKeyKyberErrNoPanicWPlaced M A lim H)
    (hOk : PreKey830OkNoPanicWPlaced M A lim H) :
    PreKey684OkNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons hv3 hv4 hlen hdec hbkO
    hikO hmsgO hspkO hreg hopk hkpk hd hst hbkC hikC hmsgC hpc hrun
  rcases w8b_kyber_dispatch m.kyberPreKeyId m.kyberCiphertext vb with hokY | herrY
  swap
  · exact hErr x st s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberCap kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons hv3 hv4 hlen
      hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd herrY hst hbkC hikC hmsgC hpc hrun
  have hok684 := ky_kyber_ok_cond hokY
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
      ((memRegion (s0.sp - 608#64 + 12#64) 4 ∗
          seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
            ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
            regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
          memRegion (s0.sp - 608#64 + 112#64) 32 ∗
          ((s0.sp - 608#64 + 312#64) ↦₈ 0#8) ∗
          ((s0.sp - 608#64 + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (s0.sp - 608#64 + 345#64) 15 ∗
          A.pool lim st sf ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
        w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr
          msgCap msgPtr bk ik msg x.bytes))
    (by
      unfold w8bRowKPostPlaced w8bRowKFrame w8bRowYFramePlaced seg1SpillsAtW
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc, CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, optVecU8Buf]
      rw [w8b_memRegion16_split (s0.sp - 608#64), w8b_memRegion184_split (s0.sp - 608#64)]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (sepConj_mono_left (ky_optVecU8Buf_cap_bnd A.repAlloc kyberCap kyberPtr kyberLen m.kyberCiphertext)) ?_
  rw [sepConj_assoc]
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun hbnd => ?_
  have hfitBox := fitsEnv_pksmFrom684_ok_box hok684 hbnd hfit
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      (memRegion (s0.sp - 608#64 + 12#64) 4 ∗
        seg1SpillsAtW (s0.sp - 608#64) bkCap bkPtr (BitVec.ofNat 64 bk.length) kyberLen
          ikPtr (BitVec.ofNat 64 ik.length) msgPtr (BitVec.ofNat 64 msg.length)
          regTag regVal opkTag opkVal spkId kpkTag kpkVal ∗
        memRegion (s0.sp - 608#64 + 112#64) 32 ∗
        ((s0.sp - 608#64 + 312#64) ↦₈ 0#8) ∗
        ((s0.sp - 608#64 + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
        memRegion (s0.sp - 608#64 + 345#64) 15 ∗
        optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
        A.pool lim st sf ∗ stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap ikPtr
        msgCap msgPtr bk ik msg x.bytes)
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic
    (w5b_kyber_ok_placed_wpW (kpkOpt := m.kyberPreKeyId) (kyberOpt := m.kyberCiphertext) hC
      hfitBox (by revert hkpk; cases m.kyberPreKeyId <;> exact fun h => h) hokY hst hpc hrun) ?_
  rintro sm Pm hpcm hrunm ⟨evs₁, kyberBoxPtr, kyberBoxLen,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p31, w9, w13, w15, w23, hevs₁, hpkb, hkst, hPm⟩
  have hfit830 := fitsEnv_pksmFrom684_ok_step hok684 hbnd hevs₁ hfit
  refine CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.SepWPp.mono_post
    (CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (sepConj_mono_left hPm)
      (hOk x (M.stepEvents evs₁ st) s0 sm vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr
        msgCap msgPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen
        p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 hfit830 hcons hv3 hv4 hlen hdec hbkO hikO
        hmsgO hspkO hreg hopk hkpk hd hokY hpkb hkst hbkC hikC hmsgC hpcm hrunm)) ?_
  intro sf' Pf _ _ hq
  exact w8bRetPost_prepend (fun _ h2 => pksmFrom684Env_of_ok hok684 hbnd hevs₁ h2) hq

end Kyber

section ErrKyber

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA (preKeyNoPanicQp w8b_bind_frame_noPanic w8b_errTail_close_noPanic_placed)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (InvalidMessageReason PublicKey SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111)
open CryptoVerification.E2E.Pqxdh.ResponderWire (memRegion32_112_pack preKeyCalleeSavedAt preKeyPlacedProg preKeyTryFromSubStack spUnused112)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (deallocSlot entails_of_eq exists_pkBytesOf optVecU8Buf sevenBytesHeadAt)
open CryptoVerification.LibsignalTripleRatchetRepr (invalidMessageStrAt noneCap speAt)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (BaseKeyOkStatePlaced KyberExitA24StatePlaced pkOf pksmErrE pksmParse_eq_none_of_w5b_kyber_err w8bKyberErr684FramePlaced w8bKyberErrA24RestPlaced w8bKyberErr_open_a24_placed w8bKyberErr_placed_pack w8bOptU32Cells w8bRowKFrame w8bRowKPostPlaced w8bRowK_open_kyberErr_placed)
open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Heap (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FitsEvents FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (CodecHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (PksmCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (PksmFrom684Env pksmFrom684PreEnv_of_half pksmFrom684PreEnv_of_v4)

private theorem eky_vecU8_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : BitVec 64) (bs : List (BitVec 8)) :
    CryptoVerification.RustHeap.vecU8 (A.atState lim st s) v bs = CryptoVerification.RustHeap.vecU8 A.repAlloc v bs := by
  simp only [CryptoVerification.RustHeap.vecU8, CryptoVerification.RustHeap.vecU8At,
    LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc]

private theorem eky_invalidMessageStrAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt (A.atState lim st s) a r = invalidMessageStrAt A.repAlloc a r := by
  cases r <;> simp only [invalidMessageStrAt, eky_vecU8_atState_eq]

private theorem eky_pksmErrE_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (fn : List (BitVec 8))
    (sret : BitVec 64) (e : SignalProtocolError) :
    pksmErrE (A.atState lim st s) fn sret e = pksmErrE A.repAlloc fn sret e := by
  cases e <;> simp only [pksmErrE, speAt, eky_vecU8_atState_eq, eky_invalidMessageStrAt_atState_eq]

private theorem eky_freeOnlyEvs_append {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyEvs evs₁) (h2 : FreeOnlyEvs evs₂) :
    FreeOnlyEvs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with h | h
  · exact h1 ev h
  · exact h2 ev h

private theorem eky_pksmFrom684Env_append_freeOnly
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {evs₁ evs₂ : List AllocEvent}
    (h1 : PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt evs₁)
    (h2 : FreeOnlyEvs evs₂) :
    PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt (evs₁ ++ evs₂) := by
  rcases h1 with ha | ⟨evs_a, evs_f, rfl, ha, hf⟩
  · exact Or.inr ⟨evs₁, evs₂, rfl, ha, h2⟩
  · exact Or.inr ⟨evs_a, evs_f ++ evs₂, List.append_assoc _ _ _, ha, eky_freeOnlyEvs_append hf h2⟩

private theorem eky_fitsEvents_of_pksmFrom684_half
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (hhalf : (kpkOpt.isSome != kyberOpt.isSome) = true)
    (hfit : FitsEnv M lim st (PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt)) :
    FitsEvents M lim st (rustAllocEvents 68 1) := by
  apply hfit
  exact Or.inl (by rw [pksmFrom684PreEnv_of_half hhalf])

private theorem eky_fitsEvents_of_pksmFrom684_v4
    {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    (hv4 : kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat)
    (hfit : FitsEnv M lim st (PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt)) :
    FitsEvents M lim st (rustAllocEvents 54 1) := by
  apply hfit
  exact Or.inl (by rw [pksmFrom684PreEnv_of_v4 hv4])

theorem w8bKyberErr_684_to_a24_noPanic_placed_wpE [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) (hC : PksmCalleesPlaced M A lim H)
    {st : M.σ} {s0 s : State}
    {sp' sret len ptr0 kyberCap kyberPtr kyberLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {xBytes ik msg : List (BitVec 8)}
    {kpkTag kpkVal : BitVec 32}
    {kpkOpt : Option (BitVec 32)} {kyberOpt : Option (List (BitVec 8))}
    {bk : List (BitVec 8)} {pk : PublicKey}
    (hfit : FitsEnv M lim st (PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt))
    (hkpk : w8bOptU32Cells kpkOpt (kpkTag, kpkVal))
    (herr : (kpkOpt.isSome != kyberOpt.isSome) = true ∨
      (kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat))
    (hst : BaseKeyOkStatePlaced s0 sp' sret len ptr0 kyberCap kyberPtr ikCap msgCap vb bk pk s)
    (hpc : s.pc = (blkPl_111).base + 1668#64)
    (hrun : s.status = .Running) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2596#64) s
      ((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15) ∗
        (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool lim st s ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      (fun sf Pf =>
        ∃ evs₁ : List AllocEvent,
          PksmFrom684Env vb xBytes ik msg kpkOpt kyberOpt evs₁ ∧
          KyberExitA24StatePlaced s0 sp' sret len ptr0 ikCap msgCap vb sf ∧
          (Pf ⊢ (pksmErrE A.repAlloc [] sret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap) ∗
            ((sp' + 68#64) ↦₃₂ kpkTag) ∗
            memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
            A.pool lim (M.stepEvents evs₁ st) sf ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)))
      preKeyNoPanicQp := by
  rcases hst with ⟨hst_ep, _, _, hpk_bytes,
    hx29, hx28, hx27, hx26, hx25, _, hx23, hx22, hx21, hx20, hx19⟩
  have hlen32 : ((bk.take 33).drop 1).length = 32 := by
    rw [← hpk_bytes]; exact (pkOf bk).bytes.toList_length
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk_of⟩ :=
    exists_pkBytesOf ((bk.take 33).drop 1) hlen32
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      ((((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗
          ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (sp' + 345#64) 15 ∗ A.pool lim st s) ∗
        (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine w8b_bind_frame_noPanic
    (W5bKyberWPlacedBudget.pk_scatter_head_placed_wp hpk_of hst_ep hpc hrun hx29 hx28 hx27 hx26 hx25 hx23 hx22 hx21
      hx20 hx19) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hst1, hpstate1, _, _, _,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, _, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1, hent1⟩
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre (P' :=
      (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
        memRegion sret 248 ∗ A.pool lim st s1 ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
      (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 312#64) 48))
    (by
      refine Entails.trans (sepConj_mono_left hent1) ?_
      refine Entails.trans (Q :=
        (spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6) ∗
        (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen kyberOpt ∗
          memRegion sret 248 ∗ A.pool lim st s1 ∗ stackAt sp' (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100)) ∗
        (((sp' + 68#64) ↦₃₂ kpkTag) ∗ memRegion (sp' + 312#64) 48))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left hm112) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  rcases herr with hhalf | ⟨rfl, rfl, hvb_ge⟩
  · have htag : kpkTag = if kpkOpt.isSome then 1#32 else 0#32 := by
      cases kpkOpt with
      | some _ => exact hkpk.1
      | none => exact hkpk
    have hfit68 := eky_fitsEvents_of_pksmFrom684_half hhalf hfit
    refine W8bNoPanicAuxA.w8b_frame_noPanic
      (W5bKyberWPlacedBudget.kyber_half_err_placed_wpE hH hC hfit68 htag hhalf hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, evs_d, hfree_d, hentf⟩ => ?_
    refine ⟨rustAllocEvents 68 1 ++ evs_d,
      Or.inr ⟨rustAllocEvents 68 1, evs_d, rfl, by rw [pksmFrom684PreEnv_of_half hhalf], hfree_d⟩,
      hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; sep_ac_rfl
  · have hkpk0 : kpkTag = 0#32 := hkpk
    subst hkpk0
    have hfit54 := eky_fitsEvents_of_pksmFrom684_v4 ⟨rfl, rfl, hvb_ge⟩ hfit
    refine W8bNoPanicAuxA.w8b_frame_noPanic
      (W5bKybercWPlacedBudget.kyber_neither_v4_err_placed_wpE hH hfit54 hvb_ge hst1 hpc1 hrun1 hpstate1
        hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1)
      fun sf Pf ⟨hstf, hentf⟩ => ?_
    refine ⟨rustAllocEvents 54 1,
      Or.inl (by rw [pksmFrom684PreEnv_of_v4 ⟨rfl, rfl, hvb_ge⟩]),
      hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hentf) ?_
    apply entails_of_eq; sep_ac_rfl

theorem preKeyKyberErrNoPanicW_placed_proof [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hH : CodecHooksPlaced M A lim H) (hC : PksmCalleesPlaced M A lim H) :
    PreKeyKyberErrNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberCap
    kyberPtr kyberLen regTag regVal opkTag opkVal kpkTag kpkVal hfit hcons _hv3 _hv4 _hlen hdec
    _hbkO _hikO _hmsgO _hspkO _hreg _hopk hkpk _hd herrY hst hbkC hikC hmsgC hpc hrun
  have hparse : CryptoVerification.SignalSession.Cli.RunProofs.Pksm.pksmParse x.bytes = none :=
    hcons ▸ pksmParse_eq_none_of_w5b_kyber_err hdec herrY
  have hbkNe : bkCap ≠ noneCap := by rintro rfl; revert hbkC; decide
  have hikNe : ikCap ≠ noneCap := by rintro rfl; revert hikC; decide
  have hmsgNe : msgCap ≠ noneCap := by rintro rfl; revert hmsgC; decide
  have hopen0 := w8bRowK_open_kyberErr_placed (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret
    x.ptr bkCap bkPtr kyberCap kyberPtr kyberLen ikCap ikPtr msgCap msgPtr regTag regVal opkTag
    opkVal spkId kpkTag kpkVal m.kyberCiphertext bk ik msg x.bytes
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := ((((s0.sp - 608#64 + 68#64) ↦₃₂ kpkTag) ∗ memRegion (s0.sp - 608#64 + 112#64) 32 ∗
          ((s0.sp - 608#64 + 312#64) ↦₈ 0#8) ∗
          ((s0.sp - 608#64 + 313#64) ↦ₛ (bk.take 33).drop 1) ∗
          memRegion (s0.sp - 608#64 + 345#64) 15) ∗
        (optVecU8Buf A.repAlloc kyberCap kyberPtr kyberLen m.kyberCiphertext ∗
          memRegion x.ret 248 ∗ A.pool lim st sf ∗
          stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100))) ∗
      w8bKyberErr684FramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ptr bkCap bkPtr kyberLen ikCap
        ikPtr msgCap msgPtr regTag regVal opkTag opkVal spkId kpkVal bk ik msg x.bytes)
    (by
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc, w8bRowKPostPlaced,
        w8bRowKFrame, w8bKyberErr684FramePlaced, CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, optVecU8Buf] at hopen0 ⊢
      exact Entails.of_eq hopen0) ?_
  refine w8b_bind_frame_noPanic
    (w8bKyberErr_684_to_a24_noPanic_placed_wpE hH hC hfit hkpk herrY hst hpc hrun) ?_
  rintro sm1 Pm1 hpc1 hrun1 ⟨evs₁, hevs₁,
    ⟨hst1, _hx29_1, hx26_1, hx23_1, _hx22_1, _hx21_1, _hx20_1, hx19_1⟩, hPm1⟩
  have hopen1 := w8bKyberErr_open_a24_placed (A.atState lim (M.stepEvents evs₁ st) sm1) s0
    (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
    regTag regVal opkTag opkVal spkId kpkTag kpkVal bk ik msg x.bytes
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
    (P' := ∃∗ msgAct : Bool, ∃∗ ikAct : Bool, ∃∗ bkAct : Bool,
      deallocSlot A.repAlloc msgCap msgPtr msgAct ∗ ((s0.sp - 608#64 + 96#64) ↦₆₄ msgPtr) ∗
        deallocSlot A.repAlloc ikCap ikPtr ikAct ∗ ((s0.sp - 608#64 + 104#64) ↦₆₄ ikPtr) ∗
        deallocSlot A.repAlloc bkCap bkPtr bkAct ∗
        ((s0.sp - 608#64 + 80#64) ↦₆₄ bkPtr) ∗ ((s0.sp - 608#64 + 88#64) ↦₆₄ bkCap) ∗
        A.pool lim (M.stepEvents evs₁ st) sm1 ∗
        stackAt (s0.sp - 608#64) (CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX 100) ∗
        w8bKyberErrA24RestPlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr
          (BitVec.ofNat 64 bk.length) (BitVec.ofNat 64 msg.length) kyberLen
          (BitVec.ofNat 64 ik.length) regTag regVal opkTag opkVal spkId kpkTag kpkVal x.bytes)
    (by
      refine Entails.trans (sepConj_mono_left hPm1) ?_
      dsimp only [w8bKyberErr684FramePlaced, w8bKyberErrA24RestPlaced] at hopen1 ⊢
      rw [eky_pksmErrE_atState_eq] at hopen1
      simp only [LibsignalBinary.Heap.RustCliAllocBudget.atState, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc,
        CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf, deallocSlot] at hopen1 ⊢
      exact hopen1) ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun msgAct => CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun ikAct =>
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre fun bkAct => ?_
  refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.bind
    (ErrTailCWPlacedBudget.tail_a24_placed_wpX (R := w8bKyberErrA24RestPlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr
        (BitVec.ofNat 64 bk.length) (BitVec.ofNat 64 msg.length) kyberLen
        (BitVec.ofNat 64 ik.length) regTag regVal opkTag opkVal spkId kpkTag kpkVal x.bytes)
      hC msgAct ikAct bkAct hst1 hpc1 hrun1 hx19_1 hx26_1 hx23_1 hmsgNe hikNe hbkNe) ?_
  rintro sm2 Pm2 hpc2 hrun2 ⟨hst2, _, evs₂, hfree₂, hPm2⟩
  have hpk := @w8bKyberErr_placed_pack _ (A.atState lim (M.stepEvents (evs₁ ++ evs₂) st) sm2) s0
    (s0.sp - 608#64) x.ret x.ptr (BitVec.ofNat 64 bk.length) (BitVec.ofNat 64 msg.length) kyberLen
    (BitVec.ofNat 64 ik.length) msgPtr ikPtr bkPtr bkCap regTag regVal opkTag opkVal spkId kpkTag
    kpkVal x.bytes
  have hpack' : Pm2 ⊢
      pksmErrE A.repAlloc [] x.ret (.invalidMessage .preKey .badCiphertext) ∗ anyHeap ∗
        stackAt (s0.sp - 608#64) preKeyTryFromSubStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool lim (M.stepEvents (evs₁ ++ evs₂) st) sm2 := by
    rw [← M.stepEvents_append] at hPm2
    refine Entails.trans hPm2 (Entails.trans ?_ (Entails.trans hpk ?_))
    · dsimp only [w8bKyberErrA24RestPlaced]
      rw [eky_pksmErrE_atState_eq]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
      apply entails_of_eq; sep_ac_rfl
    · rw [eky_pksmErrE_atState_eq]
      dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.atState]
      exact Entails.refl _
  exact CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre hpack'
    (w8b_errTail_close_noPanic_placed hparse (eky_pksmFrom684Env_append_freeOnly hevs₁ hfree₂) hst2 hpc2 hrun2)

end ErrKyber

section IdentKey

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxA (preKeyNoPanicQp w8b_bind_frame_noPanic w8b_call_noPanic_pk w8b_of_sepWP_end_noPanic_pk)
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoGames.LibsignalSession (PublicKey SignalProtocolError)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkLib_eq_111 blkPC_111 blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (bv_sub_add_lit' bv_sub_sub_lit keepsFrozenInv_codeRoLoaded preKeyPlacedProg)
open CryptoVerification.LibsignalTripleRatchet (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (PostEpilogueStatePlaced entails_of_eq pkBytesOf stackAt_sub_split)
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire (IdentOkStatePlaced KyberOkStatePlaced ecKeyParses identRegId pkOf w8bOptU32Cells w8bRowIFrame w8bRowIPostPlaced w8bRowYFramePlaced w8bRowYPost w8bRowY_open_ident_placed w8b_skipFieldStackX100_bounds)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget (PksmFrom830Env PksmFrom864Env pksmFrom830Env_of_ok_eq w8bRetPost)

open Arm64 ProofLib.ProgramReflection
open ProofLib hiding SepWPp
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (identityKeyTryFromSliceOkPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (blk111_noSvc0)

private abbrev ik_ikw_done := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWP.done
private abbrev ik_ikw_pure_pre := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre
private abbrev ik_ikw_exists_pre := @CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.exists_pre
private abbrev ik_ikw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev ik_ikw_of_sepWP_end_pk := @w8b_of_sepWP_end_noPanic_pk
private abbrev ik_ikw_call_noPanic_pk := @w8b_call_noPanic_pk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero

private theorem ik_ikw_identRegId_tst (regTag : BitVec 32) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) =
      (regTag &&& 1#32 == 0#32) := by
  apply congrArg (· == 0#32)
  bv_bits

private theorem ik_ikw_identRegId_csel (regTag regVal : BitVec 32) :
    (if ¬(BitVec.truncate 32 (BitVec.zeroExtend 64 regTag &&& 4294967297#64) == 0#32) = true then
        BitVec.truncate 64 regVal else 0#64) = (identRegId regTag regVal).zeroExtend 64 := by
  rw [ik_ikw_identRegId_tst]
  unfold identRegId
  by_cases h : regTag &&& 1#32 = 0#32 <;> simp [h]

private theorem ik_ikw_let_state {prog : Program} {ret : BitVec 64} {s : Arm64.State}
    {P : SepProp} {Q Qp : Arm64.State → SepProp → Prop}
    (k : let sc := s; CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret sc P Q Qp) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp prog ret s P Q Qp := k

/-- Pulls `(A.atState lim st sm).pool` out of `w8bRowIFrame` into an active left operand `L` so
`w8bRowIFrame A.repAlloc` can be framed across pure state transitions `sm → sm'`. -/
theorem w8bRowIFrame_pull_pool_noPanic [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (sm s0 : State)
    (sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen : BitVec 64)
    (opkTag opkVal spkId kpkVal : BitVec 32)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64) (vb : BitVec 8)
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    (bk ik msg bytes : List (BitVec 8)) (L : SepProp) :
    L ∗ w8bRowIFrame (A.atState lim st sm) s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap
      msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9
      w13 w15 w23 vb kpkOpt kyberOpt bk ik msg bytes =
    (L ∗ A.pool lim st sm) ∗
      w8bRowIFrame A.repAlloc s0 sp' sret ptr bkCap bkPtr kyberLen ikCap ikPtr msgCap msgPtr
        kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13
        w15 w23 vb kpkOpt kyberOpt bk ik msg bytes := by
  unfold w8bRowIFrame
  change L ∗ _ = (L ∗ A.pool lim st sm) ∗ _
  have hemp : (A.repAlloc).pool = SepProp.emp := rfl
  have hpool : (A.atState lim st sm).pool = A.pool lim st sm := rfl
  have hbuf : ∀ c p b, CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf (A.atState lim st sm) c p b =
      CryptoVerification.LibsignalTripleRatchet.Wire.vecU8Buf A.repAlloc c p b := fun _ _ _ => rfl
  have hrest : CryptoVerification.E2E.Pqxdh.ResponderWire.vecU8Rest (A.atState lim st sm) ikCap ikPtr ik =
      CryptoVerification.E2E.Pqxdh.ResponderWire.vecU8Rest A.repAlloc ikCap ikPtr ik := rfl
  have hky : CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.kyberStageOut (A.atState lim st sm)
        kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen =
      CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.kyberStageOut A.repAlloc
        kpkVal vb kpkOpt kyberOpt kyberBoxPtr kyberBoxLen := by
    cases kpkOpt <;> cases kyberOpt <;> rfl
  rw [hpool, hemp, emp_sepConj, hrest, hbuf bkCap bkPtr bk, hbuf msgCap msgPtr msg, hky]
  sep_ac_rfl

/-- (``+0x830 → +0x864`, `2096 → 2148`, `[LibsignalPlacement]``):
threads `A.pool lim st s` to `A.pool lim st sf` with zero heap events. -/
theorem preKey_ident_ok_830_to_864_noPanic_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap ikPtr ikLen : BitVec 64}
    {vb : BitVec 8} {regTag regVal : BitVec 32}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey} {S : Nat}
    (hS : 96 ≤ S) (hS64 : S ≤ 2 ^ 64)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik : CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk) (hik_len : ikLen.toNat = ik.length)
    (hst : PostEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2096#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap) (hx25 : s.readReg64 .x25 = kyberBoxLen)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H)
      ((blkPl_111).base + 2148#64) s
      ((((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
          ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
          memRegion (sp' + 144#64) 32 ∗ memRegion (sp' + 312#64) 48 ∗
          lsLogOff ∗ stackAt sp' S) ∗ A.pool lim st s)
      (fun sf Pf =>
        IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          (identRegId regTag regVal) bk pk ik ipk sf ∧
        (Pf ⊢ (((sp' + 48#64) ↦₃₂ regTag) ∗ ((sp' + 52#64) ↦₃₂ regVal) ∗
            ((sp' + 56#64) ↦₆₄ ikLen) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗ (ikPtr ↦ₛ ik) ∗
            ((sp' + 144#64) ↦ₛ ipk.bytes.toList) ∗
            ((sp' + 312#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
            memRegion (sp' + 352#64) 8 ∗
            lsLogOff ∗ stackAt sp' S) ∗ A.pool lim st sf))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hcl, htr⟩
  have hcallIk := hC.identityKeyOk
  clear hC
  have hstackIk := stackAt_sub_split sp' 96 S (by omega) hS64
  have h48_split : memRegion (sp' + 312#64) 48 =
      memRegion (sp' + 312#64) 40 ∗ memRegion (sp' + 352#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split (sp' + 312#64) 40 8 (by decide)
  rw [h48_split]
  simp only [sepConj_assoc]
  refine ik_ikw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 116) ?_
  wp_steps_sync_111 (lsmpl.base 116)
  refine ik_ikw_done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl1 => ?_
  refine ik_ikw_let_state ?_; intro sc1
  refine ik_ikw_call_noPanic_pk keepsFrozenInv_codeRoLoaded (ikPtr, ik, ipk, sp' + 312#64) hcallIk
    (by simp_all [sc1, arm64_norm]) (by simp_all [sc1, arm64_norm])
    (by dsimp only [sc1]; simpa [State.spAligned, arm64_norm] using hsp) hcl1
    (ret_pc := (blkPl_111).base + 2124#64) (by simp_all [sc1, arm64_norm])
    (T := (ikPtr ↦ₛ ik) ∗ memRegion (sp' + 312#64) 40 ∗ lsLogOff ∗ stackAt sp' 96)
    (φ := ikPtr = ikPtr ∧ ikLen.toNat = ik.length ∧
      sp' + 312#64 = sp' + 312#64 ∧ CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk)
    (by simp_all [sc1, identityKeyTryFromSliceOkPlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec,
      arm64_norm])
    ⟨rfl, hik_len, rfl, hik⟩ (by rw [hstackIk]; sep_focus)
    ?_
  clear hcallIk
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [identityKeyTryFromSliceOkPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderWire.identityKeyTryFromSliceOkPlacedSpec]
  simp only [sepConj_assoc]
  refine ik_ikw_pure_pre fun hvm2 => ik_ikw_pure_pre fun htr2 => ?_
  have hpool2 : A.pool lim st sc1 = A.pool lim st s2 :=
    (A.pool_transport lim st sc1 s2 hvm2).symm
  rw [hpool2]; clear hvm2 hpool2
  have hsc1_sp : sc1.sp = sp' := by simp [sc1, hsp_eq, arm64_norm]
  rw [hsc1_sp] at hsp2 ⊢
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2,
    hx29_2, _⟩
  dsimp only [sc1] at htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  have hsp2_eq : s2.sp = sp' := hsp2
  have h29_2 : s2.readReg64 .x29 = sp' + 512#64 := by simp [hx29_2, hx29, arm64_norm]
  have h24_2 : s2.readReg64 .x24 = sp' + 312#64 := by simp [hx24_2, hx24, arm64_norm]
  have h27_2 : s2.readReg64 .x27 = (identRegId regTag regVal).zeroExtend 64 := by
    rw [← ik_ikw_identRegId_csel]
    simp [hx27_2, arm64_norm]
  clear hsc1_sp
  obtain ⟨ik0, ik1, ik2, ik3, -, hipk⟩ :=
    exists_unpack64_of_length_32
      (List.Vector.toList_length ipk.bytes)
  rw [CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.memRegion32_words4 (sp' + 144#64), hipk]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine ik_ikw_exists_pre fun _ => ik_ikw_exists_pre fun _ =>
    ik_ikw_exists_pre fun _ => ik_ikw_exists_pre fun _ => ?_
  refine ik_ikw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps_sync_111 ((blkPl_111).base + 2148#64)
  refine ik_ikw_done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) fun hcl3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp2_eq], by tryFromPost_sp_align hsp2_align, hcl3,
      by simp [htr2, htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik,
    by simp [h29_2, arm64_norm], by simp [hx28_2, hx28, arm64_norm],
    by simp [h27_2, arm64_norm], by simp [hx26_2, hx26, arm64_norm],
    by simp [hx25_2, hx25, arm64_norm], by simp [h24_2, arm64_norm],
    by simp [hx23_2, hx23, arm64_norm], by simp [hx22_2, hx22, arm64_norm],
    by simp [hx21_2, hx21, arm64_norm], by simp [hx20_2, hx20, arm64_norm],
    by simp [hx19_2, hx19, arm64_norm]⟩, ?_⟩
  rw [hipk (sp' + 144#64), hipk (sp' + 320#64), hstackIk]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply entails_of_eq; sep_ac_rfl

/-- `+0x864` (`2148`) → `ret` after `identity_key` deserialization succeeds. -/
def PreKey864OkNoPanicWPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8))
    (spkId : BitVec 32) (pk ipk : PublicKey)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    CryptoGames.LibsignalSession.PublicKey.deserialize ik = .ok ipk →
    IdentOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb (identRegId regTag regVal) bk pk ik ipk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    FitsEnv M lim st (PksmFrom864Env x.bytes msg) →
    sf.pc = (blkPl_111).base + 2148#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowIPostPlaced (s0.sp - 608#64) ikPtr regTag regVal ik ipk ∗
        w8bRowIFrame (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr kyberLen
          ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId kpkVal p0 p1 p2 p3
          p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext bk ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom864Env x.bytes msg) x st s0)
      preKeyNoPanicQp

/-- `PreKey830OkNoPanicWPlaced` restricted to `identity_key` deserialization failure
(`PublicKey.deserialize ik = .error e`; `identity_key` `Err` edge `+0x830 → +0x978` → ret). -/
def PreKeyIdentErrNoPanicWPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  ∀ (x : CryptoVerification.SignalSession.Cli.RunCompose.PksmGhost) (st : M.σ) (s0 sf : State) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (m : ProtoPreKeySignalMessage) (bk ik msg : List (BitVec 8))
    (spkId : BitVec 32) (pk : PublicKey) (e : SignalProtocolError)
    (bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen : BitVec 64)
    (regTag regVal opkTag opkVal kpkTag kpkVal : BitVec 32)
    (kyberBoxPtr kyberBoxLen : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 : BitVec 8) (w9 : BitVec 32) (w13 : BitVec 16)
    (w15 w23 : BitVec 64),
    FitsEnv M lim st (PksmFrom830Env x.bytes ik msg) →
    x.bytes = vb :: b1 :: bs1 → ¬ (vb >>> 4) < 3#8 → ¬ 4#8 < (vb >>> 4) →
    x.bytes.length < 2 ^ 32 →
    CryptoVerification.SignalSession.Cli.RunProofs.Pksm.decodeProto (b1 :: bs1) = some m →
    m.baseKey = some bk → m.identityKey = some ik → m.message = some msg →
    m.signedPreKeyId = some spkId →
    w8bOptU32Cells m.registrationId (regTag, regVal) →
    w8bOptU32Cells m.preKeyId (opkTag, opkVal) →
    w8bOptU32Cells m.kyberPreKeyId (kpkTag, kpkVal) →
    CryptoGames.LibsignalSession.PublicKey.deserialize bk = .ok pk →
    ((m.kyberPreKeyId.isSome && m.kyberCiphertext.isSome) = true ∨
      (m.kyberPreKeyId = none ∧ m.kyberCiphertext = none ∧ vb.toNat < 0x40)) →
    (bk.take 33).drop 1 = pkBytesOf p0 p1 p2 p3 p4 p5 p6 p7 p8 w9 w13 w15 w23 p31 →
    CryptoGames.LibsignalSession.PublicKey.deserialize ik = .error e →
    KyberOkStatePlaced s0 (s0.sp - 608#64) x.ret (BitVec.ofNat 64 x.bytes.length) x.ptr
      kyberBoxPtr kyberBoxLen ikCap msgCap vb bk pk sf →
    bkCap.toNat < 2 ^ 63 → ikCap.toNat < 2 ^ 63 → msgCap.toNat < 2 ^ 63 →
    sf.pc = (blkPl_111).base + 2096#64 →
    sf.status = .Running →
    CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) sf
      (w8bRowYPost (A.atState lim st sf) (s0.sp - 608#64) bkCap bkPtr kyberLen ikPtr msgPtr
          kyberBoxPtr kyberBoxLen regTag regVal opkTag opkVal spkId kpkVal p0 p1 p2 p3 p4 p5 p6 p7
          p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext ik msg ∗
        w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap
          ikPtr msgCap msgPtr bk ik msg x.bytes)
      (w8bRetPost A lim (PksmFrom830Env x.bytes ik msg) x st s0)
      preKeyNoPanicQp

theorem preKey830OkNoPanicW_placed_of_864 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : CalleesPlacedBudget.PksmCalleesPlaced M A lim H)
    (hErr : PreKeyIdentErrNoPanicWPlaced M A lim H)
    (hOk : PreKey864OkNoPanicWPlaced M A lim H) :
    PreKey830OkNoPanicWPlaced M A lim H := by
  intro x st s0 sf vb b1 bs1 m bk ik msg spkId pk bkCap bkPtr ikCap ikPtr msgCap msgPtr kyberLen
    regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5 p6 p7 p8
    p31 w9 w13 w15 w23 hfit hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk hd hokY
    hpkb hkst hbkC hikC hmsgC hpc hrun
  cases hik : CryptoGames.LibsignalSession.PublicKey.deserialize ik with
  | error e =>
    exact hErr x st s0 sf vb b1 bs1 m bk ik msg spkId pk e bkCap bkPtr ikCap ikPtr msgCap msgPtr
      kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4 p5
      p6 p7 p8 p31 w9 w13 w15 w23 hfit hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk hkpk
      hd hokY hpkb hik hkst hbkC hikC hmsgC hpc hrun
  | ok ipk =>
    rw [pksmFrom830Env_of_ok_eq hik] at hfit ⊢
    rw [show w8bRowYFramePlaced A.repAlloc s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap
            ikPtr msgCap msgPtr bk ik msg x.bytes =
          w8bRowYFramePlaced (A.atState lim st sf) s0 (s0.sp - 608#64) x.ret x.ptr bkCap bkPtr ikCap
            ikPtr msgCap msgPtr bk ik msg x.bytes from rfl,
      w8bRowY_open_ident_placed (A.atState lim st sf)]
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.pure_pre fun ⟨hikLe, hikLt, _⟩ => ?_
    rw [w8bRowIFrame_pull_pool_noPanic A lim st sf s0]
    have hik_len : (BitVec.ofNat 64 ik.length).toNat = ik.length := by
      have h63 : (2 : Nat) ^ 63 < 2 ^ 64 := by decide
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    rcases hkst with ⟨hpost, hbk_ok, hpk_eq, hpk_bytes, hx29, hx28, _hx27, hx26, hx25, hx24, hx23,
      hx22, hx21, hx20, hx19⟩
    refine w8b_bind_frame_noPanic
      (preKey_ident_ok_830_to_864_noPanic_placed_wpX (M := M) (A := A) (lim := lim) (st := st)
        (ikLen := BitVec.ofNat 64 ik.length) (regTag := regTag) (regVal := regVal) (ikPtr := ikPtr)
        hC w8b_skipFieldStackX100_bounds.1 w8b_skipFieldStackX100_bounds.2 hbk_ok hpk_eq
        hpk_bytes hik hik_len hpost hpc hrun hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19) ?_
    rintro sm Pm hpcm hrunm ⟨hist, hPm⟩
    refine CryptoVerification.LibsignalTripleRatchet.Wire.SepWPp.mono_pre
      (Entails.trans (sepConj_mono_left hPm)
        (Entails.of_eq (w8bRowIFrame_pull_pool_noPanic A lim st sm s0 (s0.sp - 608#64) x.ret x.ptr bkCap
          bkPtr kyberLen ikCap ikPtr msgCap msgPtr kyberBoxPtr kyberBoxLen opkTag opkVal spkId
          kpkVal p0 p1 p2 p3 p4 p5 p6 p7 p8 p31 w9 w13 w15 w23 vb m.kyberPreKeyId m.kyberCiphertext
          bk ik msg x.bytes
          (w8bRowIPostPlaced (s0.sp - 608#64) ikPtr regTag regVal ik ipk)).symm))
      (hOk x st s0 sm vb b1 bs1 m bk ik msg spkId pk ipk bkCap bkPtr ikCap ikPtr msgCap msgPtr
        kyberLen regTag regVal opkTag opkVal kpkTag kpkVal kyberBoxPtr kyberBoxLen p0 p1 p2 p3 p4
        p5 p6 p7 p8 p31 w9 w13 w15 w23 hcons hv3 hv4 hlen hdec hbkO hikO hmsgO hspkO hreg hopk
        hkpk hd hokY hpkb hik hist hbkC hikC hmsgC hfit hpcm hrunm)

end IdentKey

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bNoPanicAuxC
