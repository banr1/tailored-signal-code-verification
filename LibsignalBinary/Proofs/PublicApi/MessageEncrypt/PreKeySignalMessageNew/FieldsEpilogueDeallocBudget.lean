/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDealloc
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `PreKeySignalMessage::new` Deallocations and Exit

Relocatable `[LibsignalPlacement]` deallocation segments and `SeamB_placed → exit` composition on
block `41` for `CalleesBudget.preKeyMsgNewSpec M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget AllocCallPreserved
   VmPreserved rustDeallocEvents rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (PreKeyMsgNewEnv PreKeyMsgNewRawEnv kyberDeallocEvs preKeyMsgNewRawEvents preKeyMsgNewSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (SeamB_placed)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueBudget
  (preKeyMsg_sret_stores_wp_placed preKeyMsg_dealloc_placed_ok)
open CryptoGames.LibsignalSession (macLength)
open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsRustDeallocSym lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageAt)
open CryptoVerification.LibsignalTripleRatchet (boxU8Buf)
open CryptoVerification.LibsignalPublicApiRepr (PreKeyMsgGhost optKyberAt preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall preKeyMsgNewStack)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost preKeyMsgSubStack preKeyMsgSavedRegs optKyberCopyBuf
   vecU8AtLen preKeyMsgFrameSlotsAt' preKeyMsgHeapAt)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
  (entails_of_sep_focus stackAt_preKeyMsgSub_to_allocHook stackAt_preKeyMsgNew_to_allocHook
   bitVec_ofNat_slt_one_eq_false publicKey_serialize_length identityKey_serialize_length
   not_satisfies_false_sepConj2 preKeyMsgFrameRest preKeyMsgFrameRest_entails_stackAt
   preKeyMsg_seq_wp' signalMessageBounds_of_seamB)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem preKeyMsg_seq_wpp_npan {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop} {Q : State → SepProp → Prop}
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q (fun _ _ => False)) :
    SepWPp prog ret s P Q (fun _ _ => False) := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hp⟩ | ⟨_, _hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ := h2 sm hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact hp.elim
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem preKeyMsg_dealloc_kyber_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64) (st : M.σ)
    (s : State)
    (hpc : s.pc =
      if (match x.kp with
          | none => noneCap
          | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (blkPl_41).base + 1428#64
      else
        (blkPl_41).base + 1412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1428#64)
      s
      (optKyberCopyBuf A.repAlloc g.kyberCopyPtr x.kp ∗
       ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗
          A.pool lim (M.stepEvents (kyberDeallocEvs x.kp) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  cases hkp : x.kp with
  | none =>
    simp only [hkp, kyberDeallocEvs, AllocCostModel.stepEvents_nil,
      show noneCap.slt 1#64 = true by decide, ↓reduceIte,
      optKyberCopyBuf, emp_sepConj] at hpc ⊢
    exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
      Entails.refl _⟩
  | some k =>
    simp only [hkp, kyberDeallocEvs, optKyberCopyBuf, boxU8Buf,
      RustCliAllocBudget.repAlloc_live, sepConj_assoc] at hpc hx19 ⊢
    refine SepWPp.pure_elim fun ⟨_, hkb⟩ => ?_
    by_cases hct : k.ciphertext = []
    · simp only [hct, ↓reduceIte, AllocCostModel.stepEvents_nil, List.length_nil,
        show (BitVec.ofNat 64 0).slt 1#64 = true by decide, emp_sepConj] at hpc ⊢
      exact SepWPp.done hpc hrun ⟨⟨hsp, hsp_align, hx20, hx22, hx24, hx27, hx28, hx29, rfl, rfl⟩,
        Entails.refl _⟩
    · have hct_pos : 0 < k.ciphertext.length := List.length_pos_iff.mpr hct
      have hslt : (BitVec.ofNat 64 k.ciphertext.length).slt 1#64 = false :=
        bitVec_ofNat_slt_one_eq_false k.ciphertext.length hct_pos (by omega)
      have htoNat : (BitVec.ofNat 64 k.ciphertext.length).toNat = k.ciphertext.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hslt, Bool.false_eq_true, ↓reduceIte, hct, sepConj_assoc] at hpc ⊢
      have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
      wp_steps_sync_pool (lsρ lsRustDeallocSym)
      refine SepWPp.call_wpp (x := (g.kyberCopyPtr, k.ciphertext.length, 1, st))
        (F := ((sp0 - 320#64) ↦₆₄ g.kyberCopyPtr) ∗ memRegion (sp0 - 368#64 - 7824#64) 3728)
        hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned, arm64_norm] using hsp_align)
        (by simp only [arm64_norm]; rfl) ?_
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
      · intro R' hm
        have hmem := pointsToBytes_entails_memRegion g.kyberCopyPtr k.ciphertext
        rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
        simp (config := { decide := true }) only [rustCliDeallocBudgetSpec, sepConj_assoc,
          wp_norm, arm64_norm, *] at hm ⊢
        refine Satisfies.mono ?_ hm
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem)))
        exact entails_of_sep_focus (by sep_focus)
      intro sf1 hpc1 hrun1 hsp1 hcs1
      rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
      simp only [rustCliDeallocBudgetSpec, AllocCallPreserved, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨⟨_, _, htr1, _⟩, _⟩ => ?_
      have hsp_align1 : sf1.spAligned = true := by
        rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
      refine SepWPp.done hpc1 hrun1 ⟨?_, ?_⟩
      · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align1,
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      · rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
        simp only [hsp, wp_norm, arm64_norm]
        exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_bk_ik_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 : BitVec 64) (st : M.σ)
    (s : State)
    (hpc : s.pc = (blkPl_41).base + 1428#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp (lsProg_41 H)
      ((blkPl_41).base + 1468#64)
      s
      (boxU8Buf A.repAlloc g.bkSerPtr x.baseKey.serialize ∗
       boxU8Buf A.repAlloc g.ikSerPtr x.ik.serialize ∗
       ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
       A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1) st) sm ∗
          stackAt (sp0 - 368#64) preKeyMsgSubStack))
      (fun _ _ => False) := by
  have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
  have hbk_len := publicKey_serialize_length x.baseKey
  have hbk_ne : x.baseKey.serialize ≠ [] := by
    intro h; rw [h] at hbk_len; simp at hbk_len
  have hik_len := identityKey_serialize_length x.ik
  have hik_ne : x.ik.serialize ≠ [] := by
    intro h; rw [h] at hik_len; simp at hik_len
  unfold boxU8Buf
  simp only [hbk_ne, hik_ne, ↓reduceIte, hbk_len, hik_len,
    RustCliAllocBudget.repAlloc_live, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  have hpull_ik :
      A.live g.bkSerPtr 33 1 ∗
        (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
        ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        A.live g.ikSerPtr 33 1 ∗
        (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
        ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
        A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack =
      ⌜g.ikSerPtr ≠ 0#64 ∧ (33 : Nat) < 2 ^ 63⌝ ∗
        (A.live g.bkSerPtr 33 1 ∗
         (g.bkSerPtr ↦ₛ x.baseKey.serialize) ∗
         A.live g.ikSerPtr 33 1 ∗
         (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
         ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
         A.pool lim st s ∗ stackAt (sp0 - 368#64) preKeyMsgSubStack) := by sep_focus
  rw [hpull_ik]
  clear hpull_ik
  refine SepWPp.pure_elim fun _ => ?_
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  refine SepWPp.call_wpp (x := (g.bkSerPtr, 33, 1, st))
    (F := A.live g.ikSerPtr 33 1 ∗
          (g.ikSerPtr ↦ₛ x.ik.serialize) ∗
          ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  · intro R' hm
    have hmem_bk := pointsToBytes_entails_memRegion g.bkSerPtr x.baseKey.serialize
    rw [hbk_len] at hmem_bk
    rw [stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)] at hm
    simp (config := { decide := true }) only [rustCliDeallocBudgetSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_bk)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1, hvregs_1⟩
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨⟨_, _, htr1, _⟩, _⟩ => ?_
  have hsp_align1 : sf1.spAligned = true := by
    rw [State.spAligned, hsp1]; simpa [State.spAligned, arm64_norm] using hsp_align
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  refine SepWPp.call_wpp (x := (g.ikSerPtr, 33, 1, M.stepEvents (rustDeallocEvents 33 1) st))
    (F := ((sp0 - 352#64) ↦₆₄ g.ikSerPtr) ∗
          memRegion (sp0 - 368#64 - 7824#64) 3728)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, arm64_norm] using hsp_align1)
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  · intro R' hm
    have hmem_ik := pointsToBytes_entails_memRegion g.ikSerPtr x.ik.serialize
    rw [hik_len] at hmem_ik
    simp (config := { decide := true }) only [rustCliDeallocBudgetSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_ik)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf2 hpc2 hrun2 hsp2 hcs2
  rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨⟨_, _, htr2, _⟩, _⟩ => ?_
  have hsp_align2 : sf2.spAligned = true := by
    rw [State.spAligned, hsp2]; simpa [State.spAligned, arm64_norm] using hsp_align1
  refine SepWPp.done hpc2 hrun2 ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *], hsp_align2,
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [M.stepEvents_append, stackAt_preKeyMsgSub_to_allocHook (sp0 - 368#64)]
    simp only [hsp1, hsp, wp_norm, arm64_norm]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_dealloc_msg_and_epilogue_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64) (st : M.σ)
    (hmsg_lo : macLength + 1 ≤ x.msg.serialized.length)
    (hmsg_hi : x.msg.serialized.length < 2 ^ 40)
    (s0 s : State)
    (hpc : s.pc = (blkPl_41).base + 1468#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = g.msgCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by
      first
      | assumption
      | simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (lsProg_41 H)
      (s0.readReg64 .lr)
      s
      (boxU8Buf A.repAlloc g.msgCopyPtr x.msg.serialized ∗
       preKeyMsgSavedRegs sp0 s0 ∗
       preKeyMsgFrameRest x g sp0 lenW ∗
       A.pool lim st s ∗
       stackAt (sp0 - 368#64) preKeyMsgSubStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢ A.pool lim (M.stepEvents (rustDeallocEvents x.msg.serialized.length 1) st) sf ∗
          stackAt s0.sp preKeyMsgNewStack))
      (fun _ _ => False) := by
  let _ := hlr_ls
  have hsp_cancel : sp0 - 368#64 + 368#64 = sp0 := BitVec.sub_add_cancel sp0 368#64
  have hmsg_pos : 0 < x.msg.serialized.length := by unfold macLength at hmsg_lo; omega
  have hmsg_ne : x.msg.serialized ≠ [] := by
    intro h; simp [h] at hmsg_pos
  have hmsg_toNat : (BitVec.ofNat 64 x.msg.serialized.length).toNat = x.msg.serialized.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmsg_ne0 : BitVec.ofNat 64 x.msg.serialized.length ≠ 0#64 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [hmsg_toNat, BitVec.toNat_zero] at ht
    omega
  have hmsg_beq : (BitVec.ofNat 64 x.msg.serialized.length == 0#64) = false :=
    beq_eq_false_iff_ne.mpr hmsg_ne0
  have hdealloc_ok := preKeyMsg_dealloc_placed_ok hdealloc
  unfold boxU8Buf
  simp only [hmsg_ne, ↓reduceIte, RustCliAllocBudget.repAlloc_live, sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  unfold preKeyMsgSavedRegs
  simp only [sepConj_assoc]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  refine SepWPp.call_wpp (x := (g.msgCopyPtr, x.msg.serialized.length, 1, st))
    (ret_pc := s0.readReg64 .lr)
    (F := memRegion (sp0 - 8192#64) 4096)
    hdealloc_ok (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
    (by simp only [wp_norm, arm64_norm, *]) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ ⟨_, hm⟩ => not_satisfies_false_sepConj hm) ?_
  · intro R' hm
    have hst := preKeyMsgFrameRest_entails_stackAt x g s0 sp0 lenW
    unfold preKeyMsgSavedRegs at hst
    rw [stackAt_preKeyMsgNew_to_allocHook sp0,
      sepConj_comm (memRegion (sp0 - 8192#64) 4096)] at hst
    have hmem_msg := pointsToBytes_entails_memRegion g.msgCopyPtr x.msg.serialized
    simp (config := { decide := true }) only [rustCliDeallocBudgetSpec, sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    rw [← sepConj_assoc (stackAt sp0 allocHookStack)]
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_msg (sepConj_mono_left hst))))
    exact entails_of_sep_focus (by sep_focus)
  intro sf hpcf hrunf hspf hcsf
  rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f, hvregs_f⟩
  simp only [rustCliDeallocBudgetSpec, AllocCallPreserved, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨⟨_, _, htr_f, _⟩, _⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
  · refine ⟨by simp only [wp_norm, arm64_norm, *],
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
      by simp only [wp_norm, arm64_norm, *]⟩
  · rw [hsp0, stackAt_preKeyMsgNew_to_allocHook sp0]
    simp only [wp_norm, arm64_norm, *]
    exact entails_of_sep_focus (by sep_focus)

theorem preKeyMsg_reaches_outcome_of_sepWPp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {st : M.σ} {evs_tot : List AllocEvent} {P R : SepProp} {s0 s : State}
    (hevs : PreKeyMsgNewEnv x evs_tot)
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_41 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        (sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) ∧
        (P_f ⊢
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A.repAlloc g' x.ret x.model) ∗
          (s0.sp ↦₆₄ x.msgA) ∗
          memRegion x.kyA 24 ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗
          memRegion x.msgA 120 ∗
          A.pool lim (M.stepEvents evs_tot st) sf ∗
          stackAt s0.sp preKeyMsgNewStack))
      (fun _ _ => False)) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, ⟨hspf, hcsf, htrf⟩, hent⟩ | ⟨_, _, _, hqp⟩ | ⟨_, _hoom⟩⟩ :=
    hwp R hm hL
  · refine reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcsf⟩, ?_⟩))
    have hpost : P_f ⊢ (preKeyMsgNewSpec M A lim).post (x, st) s0 sf := by
      dsimp only [preKeyMsgNewSpec,
        CryptoVerification.LibsignalPublicApi.MessageEncrypt.preKeyMsgNewSpec]
      refine Entails.sepExists_right evs_tot ?_
      exact Entails.pure_right hevs (Entails.pure_right htrf hent)
    exact Satisfies.mono (sepConj_mono_left hpost) hmf
  · exact hqp.elim
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

private theorem optKyberAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberAt (A.atState lim st s) a ptr kp = optKyberAt A.repAlloc a ptr kp := by
  cases kp <;> rfl

private theorem signalMessageAt_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g a m) :
    signalMessageAt (A.atState lim st s) g a m = signalMessageAt A.repAlloc g a m := rfl

private theorem vecU8AtLen_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v cap ptr lenW : BitVec 64) (bs : List (BitVec 8)) :
    vecU8AtLen (A.atState lim st s) v cap ptr lenW bs =
      vecU8AtLen A.repAlloc v cap ptr lenW bs := rfl

private theorem optKyberCopyBuf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (kp : Option KyberPayload) :
    optKyberCopyBuf (A.atState lim st s) ptr kp = optKyberCopyBuf A.repAlloc ptr kp := by
  cases kp <;> rfl

private theorem boxU8Buf_atState_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    boxU8Buf (A.atState lim st s) ptr bs = boxU8Buf A.repAlloc ptr bs := rfl

theorem fields_epilogue_placed_ok_aux [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {x : PreKeyMsgNewCall} {st : M.σ} {g : PreKeyMsgFrameGhost} {R : SepProp} {s0 s : State}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hB : SeamB_placed A lim x st g R s0 s) :
    reaches_outcome (lsProg_41 H) (preKeyMsgNewSpec M A lim) (x, st) R s0 s := by
  rcases hB with ⟨evs, hevs, hlr0, hpc, _hcl, ⟨hser_bound, hver, hpre, _⟩,
    ⟨hrun, hsp, hsp0_align, hsp_align, htr, hx29, hx19, hx20, hx21, hx22, hx24, hx25, hx27, hx28, hvregs⟩,
    hx8, hx23, hx26, lenW, hm⟩
  have ⟨hmsg_lo, hmsg_hi⟩ := signalMessageBounds_of_seamB hm
  let evs_tot := evs ++ kyberDeallocEvs x.kp ++
    (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    rustDeallocEvents x.msg.serialized.length 1
  have hevs_tot : PreKeyMsgNewEnv x evs_tot := by
    dsimp only [PreKeyMsgNewEnv, PreKeyMsgNewRawEnv, preKeyMsgNewRawEvents, evs_tot, kyberDeallocEvs]
    rw [hevs]
  have hsp' : s.sp = s0.sp - 368#64 := hsp
  have hx29' : s.readReg64 .x29 = s0.sp - 96#64 := hx29
  rw [← sepConj_assoc] at hm
  refine preKeyMsg_reaches_outcome_of_sepWPp_placed (evs_tot := evs_tot) hevs_tot hm ?_
  have hsret_wp :=
    (preKeyMsg_sret_stores_wp_placed (A := A.repAlloc) (H := H) x g s0.sp lenW hser_bound hver hpre s
      hpc hrun hsp' hsp_align hx8 hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29').mono
      (fun _ _ _ _ ⟨h1, h2, h3⟩ => And.intro (And.intro h1 h2) h3)
  refine preKeyMsg_seq_wp' hsret_wp
    (by
      (conv => lhs; simp only [preKeyMsgFrameSlotsAt', preKeyMsgHeapAt,
        optKyberAt_atState_eq, signalMessageAt_atState_eq, vecU8AtLen_atState_eq,
        optKyberCopyBuf_atState_eq, boxU8Buf_atState_eq,
        RustCliAllocBudget.atState_pool, sepConj_assoc, arm64_norm])
      sep_focus) ?_
  intro s1 hpc1 hrun1 ⟨hvm1, ⟨hsp1, hsp_align1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hvregs1⟩⟩
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hvregs1' : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  have hpool1 : A.pool lim (M.stepEvents evs st) s = A.pool lim (M.stepEvents evs st) s1 :=
    (A.pool_of_vmPreserved hvm1).symm
  refine preKeyMsg_seq_wpp_npan
    (preKeyMsg_dealloc_kyber_wpp_placed hdealloc x g s0.sp (M.stepEvents evs st) s1
      hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
    (by rw [hpool1]; sep_focus) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hvregs2⟩
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hvregs2' : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans hvregs1'
  refine preKeyMsg_seq_wpp_npan
    (preKeyMsg_dealloc_bk_ik_wpp_placed hdealloc x g s0.sp
      (M.stepEvents (kyberDeallocEvs x.kp) (M.stepEvents evs st)) s2
      hpc2 hrun2 hsp2 hsp_align2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx20_3, hx27_3, _hx29_3, htr3, hvregs3⟩
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hvregs3' : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans hvregs2'
  refine preKeyMsg_seq_wpp_npan
    (preKeyMsg_dealloc_msg_and_epilogue_wpp_placed hdealloc x g s0.sp lenW
      (M.stepEvents (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1)
        (M.stepEvents (kyberDeallocEvs x.kp) (M.stepEvents evs st)))
      hmsg_lo hmsg_hi s0 s3 hpc3 hrun3 hsp3 rfl hsp0_align hsp_align3 hx20_3 hx27_3 htr3' hvregs3')
    (by (conv => rhs; arg 1; simp only [preKeyMsgFrameRest, sepConj_assoc, arm64_norm]); sep_focus) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  have hstep_eq :
      M.stepEvents (rustDeallocEvents x.msg.serialized.length 1)
        (M.stepEvents (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1)
          (M.stepEvents (kyberDeallocEvs x.kp) (M.stepEvents evs st))) =
      M.stepEvents evs_tot st := by
    simp only [evs_tot, M.stepEvents_append]
  rw [hstep_eq]
  exact entails_of_sep_focus (by sep_focus)

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget
