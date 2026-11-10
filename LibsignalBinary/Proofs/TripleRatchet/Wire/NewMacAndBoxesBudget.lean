/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Phase 3 (`+0x3dc .. +0x628`)

Re-exports `NewMacAndBoxesBudgetAux` (`+0x3dc → +0x5ac`) and proves relocatable
`[LibsignalPlacement]` budget-threaded temporary-buffer deallocation, epilogue (`+0x5ac → ret`),
and composed Phase 3 lemmas on Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded withLsCodeLoaded lsmpl lsρ
   lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym lsMemcpySym)
open CryptoVerification.RustHeap
  (allocHookStack vecU8At)
open CryptoVerification.LibsignalProtoCodec (encode)
open CryptoGames.HMAC (keyToBytes32)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SignalMessageGhost noneCap signalMessageAt uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_63 blkPl_63 SignalMessageNewGhost TraceVRegsEq
   add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap add_one_eq_zero_iff_noneCap
   boxU8Buf computeMacStack computeMacStackX entails_newFrameRest extHookStack
   newFrameRest newFrameRest_entails_stackAt newFrameRest_entails_stackAtX
   newSavedRegs newUnusedPad optPqBuf optSerializeAddressesAt publicKey_serialize_length
   signalMessageNewStack signalMessageNewStackX stackAt_signalMessageNewGen_to_hook)
open CryptoVerification.LibsignalTripleRatchet.NewMacAndBoxesCallees
  (entails_of_sep_focus satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliDeallocBudgetExternSpecWithStack
   subroutine_ok_rustCliDeallocBudget_externWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (computeMacEvents computeMacSpec computeMacSpecWithStack computeMacSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudgetAux
  (fitsEvents_segments_of_phase3 newCtCloneEvents newDeallocPqEvents
   newDeallocRkAndCtEvents newPhase3Events newPostPrologueEvents_eq_serAlloc_append_phase3
   newPqCloneEvents new_addr_into_boxed_wp_placed
   new_compute_mac_and_append_wpp_placed new_compute_mac_and_append_wpp_placed_at
   new_compute_mac_and_append_wpp_placed_x
   new_ct_clone_wpp_placed new_ct_clone_wpp_placed_at new_ct_clone_wpp_placed_x
   new_pq_clone_wpp_placed new_pq_clone_wpp_placed_at new_pq_clone_wpp_placed_x
   new_sret_stores_wp_placed
   signalMessageNew_seq_noPanic_placed' signalMessageNew_seq_wp_placed)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_dealloc_placed_ok noAllocShimBudgetSpec)

export LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudgetAux
  (newCtCloneEvents newPqCloneEvents newDeallocRkAndCtEvents newDeallocPqEvents newPhase3Events
   newPostPrologueEvents_eq_serAlloc_append_phase3 fitsEvents_segments_of_phase3
   new_compute_mac_and_append_wpp_placed_at
   new_compute_mac_and_append_wpp_placed new_compute_mac_and_append_wpp_placed_x
   new_ct_clone_wpp_placed_at new_ct_clone_wpp_placed new_ct_clone_wpp_placed_x
   new_pq_clone_wpp_placed_at new_pq_clone_wpp_placed new_pq_clone_wpp_placed_x
   new_addr_into_boxed_wp_placed new_sret_stores_wp_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  add_one_eq_zero_iff_noneCap add_one_beq_zero_iff_noneCap add_one_bne_zero_iff_ne_noneCap

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_neg_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if ¬(v == 0#64) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_not_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (!(v == 0#64)) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_pos_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (v == 0#64) = true then a else b) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

private theorem call_noPanic_extern {α : Type} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
        intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpost).elim
  · exact (hexit sm code (F ∗ R) hex hpost).elim
  · exact (hoom sm (F ∗ R) hoom_s hpost).elim

/-! ## Deallocate `rkPtr` and `ctCopyPtr` (`+0x5ac → +0x5d8`) -/

theorem new_dealloc_rk_and_ct_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1496#64)
      s
      (boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = pqCopyPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          A.pool lim (M.stepEvents (newDeallocRkAndCtEvents x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx21 hx29
  have hdealloc := subroutine_ok_rustCliDeallocBudget_externWithStack (stk := cmStack) hle hbnd
    (new_dealloc_placed_ok h_dealloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
  have hrk_len : x.senderRatchetKey.serialize.length = 33 :=
    publicKey_serialize_length x.senderRatchetKey
  have hrk_ne : x.senderRatchetKey.serialize ≠ [] := by
    intro h; simp [h] at hrk_len
  unfold boxU8Buf
  simp only [hrk_ne, ↓reduceIte, hrk_len, A.repAlloc_live_norm, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hrkPtr_ne, _⟩ => ?_
  have hpull_ct :
      A.live rkPtr 33 1 ∗
        (rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
        ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
        (if x.ciphertext = [] then emp
         else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
        ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
        ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
        ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
        A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack =
      ⌜ctCopyPtr ≠ 0#64 ∧ x.ciphertext.length < 2 ^ 63⌝ ∗
        (A.live rkPtr 33 1 ∗
         (rkPtr ↦ₛ x.senderRatchetKey.serialize) ∗
         (if x.ciphertext = [] then emp
          else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
         ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
         ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
         ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
         A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack) := by sep_focus
  rw [hpull_ct]
  clear hpull_ct
  refine SepWPp.pure_elim fun ⟨hctPtr_ne, _⟩ => ?_
  apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  refine call_noPanic_extern (x := (rkPtr, 33, 1, st))
    (F := (if x.ciphertext = [] then emp
           else A.live ctCopyPtr x.ciphertext.length 1 ∗ (ctCopyPtr ↦ₛ x.ciphertext)) ∗
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr))
    hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
    (by simp only [arm64_norm]; rfl) ?_
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
  · intro R' hm
    have hlay_rk : RustLayoutOk 33 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
    have hmem_rk := pointsToBytes_entails_memRegion rkPtr x.senderRatchetKey.serialize
    rw [hrk_len] at hmem_rk
    dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp (config := { decide := true }) only [sepConj_assoc,
      wp_norm, arm64_norm, *] at hm ⊢
    refine Satisfies.mono ?_ hm
    refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_rk)))
    exact entails_of_sep_focus (by sep_focus)
  intro sf1 hpc1 hrun1 hsp1 hcs1
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
  simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
  dsimp only [rustCliDeallocBudgetExternSpecWithStack,
    _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  simp only [wp_norm, arm64_norm] at htr1
  let st1 := M.stepEvents (rustDeallocEvents 33 1) st
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · have hct_nil : x.ciphertext = [] := by
      have h := congrArg BitVec.toNat hct0
      simp only [BitVec.toNat_ofNat] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    have hevs_eq : newDeallocRkAndCtEvents x = rustDeallocEvents 33 1 := by
      simp [newDeallocRkAndCtEvents, hct_nil]
    rw [hevs_eq]
    simp only [hct_nil, ↓reduceIte, emp_sepConj]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 1496#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · simp only [arm64_norm]
      exact entails_of_sep_focus (by sep_focus)
  · have hct_pos : 0 < x.ciphertext.length := by
      by_contra hlt; simp [Nat.le_zero.mp (Nat.not_lt.mp hlt)] at hct0
    have hct_ne_nil : x.ciphertext ≠ [] := by
      intro h; simp [h] at hct_pos
    have hct_nonempty : x.ciphertext.isEmpty = false := List.isEmpty_eq_false_iff.mpr hct_ne_nil
    have hevs_eq :
        newDeallocRkAndCtEvents x =
          rustDeallocEvents 33 1 ++ rustDeallocEvents x.ciphertext.length 1 := by
      simp [newDeallocRkAndCtEvents, hct_nonempty]
    rw [hevs_eq, M.stepEvents_append]
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_beq : (BitVec.ofNat 64 x.ciphertext.length == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hct0
    simp only [hct_ne_nil, ↓reduceIte, sepConj_assoc]
    apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (ctCopyPtr, x.ciphertext.length, 1, st1))
      (F := ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
            ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
            ((sp0 - 344#64) ↦₆₄ ctCopyPtr))
      hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hlay_ct : RustLayoutOk x.ciphertext.length 1 :=
        ⟨⟨hct_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
      have hmem_ct := pointsToBytes_entails_memRegion ctCopyPtr x.ciphertext
      dsimp only [rustCliDeallocBudgetExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem_ct)))
      exact entails_of_sep_focus (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2, hvregs_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2 hvregs_2
    dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr2 => ?_
    simp only [wp_norm, arm64_norm, htr1] at htr2
    refine SepWPp.done hpc2 hrun2 ⟨?_, ?_⟩
    · refine ⟨hsp2, by simp only [State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align],
        h20_2, hfp_2, by simp only [wp_norm, arm64_norm, *]⟩
    · dsimp only [st1]
      simp only [hsp1, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

theorem new_dealloc_rk_and_ct_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1496#64)
      s
      (boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = pqCopyPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          A.pool lim (M.stepEvents (newDeallocRkAndCtEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_dealloc_rk_and_ct_wpp_placed_at (by decide) (by decide) h_dealloc x sp0 rkPtr ctCopyPtr
    pqCopyPtr hct_bound s hpc hrun hsp hsp_align hx19 hx21 hx29

theorem new_dealloc_rk_and_ct_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr pqCopyPtr : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1452#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 1496#64)
      s
      (boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x20 = pqCopyPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
          ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
          ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
          A.pool lim (M.stepEvents (newDeallocRkAndCtEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_dealloc_rk_and_ct_wpp_placed_at (by decide) (by decide) h_dealloc x sp0 rkPtr ctCopyPtr
    pqCopyPtr hct_bound s hpc hrun hsp hsp_align hx19 hx21 hx29

/-! ## Deallocate `pqCopyPtr` and epilogue (`+0x5d8 → s0.readReg64 .lr`) -/

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

theorem new_dealloc_pq_and_epilogue_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {hookStack : Nat} {sp0 : BitVec 64} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hbnd : hookStack + 944 ≤ 2 ^ 64 := by decide)
    (hst_entails : ∀ pqCap : BitVec 64,
      stackAt (sp0 - 416#64) (hookStack + 528) ∗
        newFrameRest sp0 ∗
        ((sp0 - 320#64) ↦₆₄ pqCap) ∗
        newSavedRegs sp0 s0 ⊢
      stackAt sp0 ((hookStack + 528) + 416))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s : State)
    (hpc : s.pc = (blkPl_63).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          A.pool lim (M.stepEvents (newDeallocPqEvents x) st) sf ∗
          stackAt s0.sp ((hookStack + 528) + 416)))
      Qp := by
  have hdealloc := subroutine_ok_rustCliDeallocBudget_externWithStack (stk := hookStack)
    hle (by omega)
    (new_dealloc_placed_ok h_dealloc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63))
  have hsp_cancel : sp0 - 416#64 + 416#64 = sp0 := BitVec.sub_add_cancel sp0 416#64
  unfold optPqBuf
  by_cases hpq : x.pqRatchet.isEmpty = true
  · have hevs_eq : newDeallocPqEvents x = [] := by simp [newDeallocPqEvents, hpq]
    rw [hevs_eq, M.stepEvents_nil]
    simp only [hpq, ↓reduceIte, sepConj_emp]
    refine SepWPp.pure_elim fun hpqCap => ?_
    subst hpqCap
    unfold newSavedRegs
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 .lr)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0]
      have hst := hst_entails noneCap
      unfold newSavedRegs at hst
      refine Entails.trans ?_ (sepConj_mono_right hst)
      exact entails_of_sep_focus (by sep_focus)
  · have hpq_false : x.pqRatchet.isEmpty = false := Bool.eq_false_iff.mpr hpq
    have hevs_eq : newDeallocPqEvents x = rustDeallocEvents x.pqRatchet.length 1 := by
      simp [newDeallocPqEvents, hpq_false]
    rw [hevs_eq]
    simp only [hpq_false, Bool.false_eq_true, ↓reduceIte, A.repAlloc_live_norm, sepConj_assoc]
    refine SepWPp.pure_elim fun hpq_pure => ?_
    rcases hpq_pure with ⟨hpqCap, hpq_pos, hpq_lt, hpqPtr_ne⟩
    subst hpqCap
    have hpqCap_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpqCap_ne : ¬(BitVec.ofNat 64 x.pqRatchet.length = 0xFFFFFFFFFFFFFFFF#64) := by
      intro h; rw [h] at hpqCap_toNat; simp at hpqCap_toNat; omega
    unfold newSavedRegs
    apply SepWPp.of_sepWP (mid := lsρ lsRustDeallocSym)
    wp_steps_sync_pool (lsρ lsRustDeallocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (pqCopyPtr, x.pqRatchet.length, 1, st))
      (ret_pc := s0.readReg64 .lr)
      (F := memRegion (sp0 - (BitVec.ofNat 64 (hookStack + 944))) 944)
      hdealloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned, hsp, hsp_cancel, ← hsp0, arm64_norm] using hsp0_align)
      (by simp only [wp_norm, arm64_norm, *]) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hlay_pq : RustLayoutOk x.pqRatchet.length 1 :=
        ⟨⟨hpq_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
      have hst := hst_entails (BitVec.ofNat 64 x.pqRatchet.length)
      unfold newSavedRegs at hst
      rw [stackAt_signalMessageNewGen_to_hook sp0 hookStack hbnd,
        sepConj_comm (memRegion (sp0 - (BitVec.ofNat 64 (hookStack + 944))) 944)] at hst
      have hmem_pq := pointsToBytes_entails_memRegion pqCopyPtr x.pqRatchet
      have hlr_ls' : LsRetAddr624 (s0.readReg64 (Reg.gpr 30#5)) := hlr_ls
      dsimp only [rustCliDeallocBudgetExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      rw [← sepConj_assoc (stackAt sp0 hookStack)]
      refine Satisfies.mono ?_ hm
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono hmem_pq (sepConj_mono_left hst))))
      exact entails_of_sep_focus (by sep_focus)
    intro sf hpcf hrunf hspf hcsf
    rcases hcsf with ⟨h19_f, h20_f, h21_f, h22_f, h23_f, h24_f, h25_f, h26_f, h27_f, h28_f, hfp_f⟩
    dsimp only [rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htr_f => ?_
    refine SepWPp.done hpcf hrunf ⟨?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩
    · rw [hsp0, stackAt_signalMessageNewGen_to_hook sp0 hookStack hbnd]
      simp only [wp_norm, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

theorem new_dealloc_pq_and_epilogue_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hpc : s.pc = (blkPl_63).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          A.pool lim (M.stepEvents (newDeallocPqEvents x) st) sf ∗
          stackAt s0.sp signalMessageNewStack))
      Qp :=
  new_dealloc_pq_and_epilogue_wpp_placed_at (hookStack := allocHookStack) (by decide) (by decide)
    (fun c => newFrameRest_entails_stackAt sp0 c s0) h_dealloc x pqCap pqCopyPtr hpq_bound s
    hpc hrun hsp hsp0 hsp0_align hsp_align hx20 htr (hlr_ls := hlr_ls)

theorem new_dealloc_pq_and_epilogue_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (x : SignalMessageNewGhost) (sp0 pqCap pqCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hpc : s.pc = (blkPl_63).base + 1496#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = pqCopyPtr)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       newSavedRegs sp0 s0 ∗
       newFrameRest sp0 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) computeMacStackX)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          A.pool lim (M.stepEvents (newDeallocPqEvents x) st) sf ∗
          stackAt s0.sp signalMessageNewStackX))
      Qp :=
  new_dealloc_pq_and_epilogue_wpp_placed_at (hookStack := extHookStack) (by decide) (by decide)
    (fun c => newFrameRest_entails_stackAtX sp0 c s0) h_dealloc x pqCap pqCopyPtr hpq_bound s
    hpc hrun hsp hsp0 hsp0_align hsp_align hx20 htr (hlr_ls := hlr_ls)

/-! ## Composed Phase 3 (`+0x3dc → s0.readReg64 .lr`) -/

theorem new_phase3_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {hookStack : Nat} {sp0 : BitVec 64} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ hookStack := by decide)
    (hbnd : hookStack + 944 ≤ 2 ^ 64 := by decide)
    (hst_entails : ∀ pqCap : BitVec 64,
      stackAt (sp0 - 416#64) (hookStack + 528) ∗
        newFrameRest sp0 ∗
        ((sp0 - 320#64) ↦₆₄ pqCap) ∗
        newSavedRegs sp0 s0 ⊢
      stackAt sp0 ((hookStack + 528) + 416))
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecWithStack M A lim C.F (hookStack + 528))))
    (x : SignalMessageNewGhost)
    (serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPhase3Events x))
    (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A.repAlloc (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) (hookStack + 528))
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret
            (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool lim (M.stepEvents (newPhase3Events x) st) sf ∗
          stackAt s0.sp ((hookStack + 528) + 416)))
      Qp := by
  have hcm_le : allocHookStack ≤ hookStack + 528 := by omega
  have hcm_bnd : hookStack + 528 ≤ 2 ^ 64 := by omega
  obtain ⟨hfit_mac, hfit_ct, hfit_pq, hstep_eq⟩ := fitsEvents_segments_of_phase3 hfit
  refine signalMessageNew_seq_noPanic_placed' hcl
    (new_compute_mac_and_append_wpp_placed_at hMac x sp0 serPtr addrCap hct_bound hpq_bound
      hfit_mac s hcl hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus) ?_
  intro s1 hcl1 hpc1 hrun1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  refine signalMessageNew_seq_noPanic_placed' hcl1
    (new_ct_clone_wpp_placed_at hcm_le hcm_bnd h_shim h_alloc h_mc x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound hfit_ct s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus) ?_
  intro s2 hcl2 hpc2 hrun2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine signalMessageNew_seq_noPanic_placed' hcl2
    (new_pq_clone_wpp_placed_at hcm_le hcm_bnd h_shim h_alloc h_mc x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound hfit_pq s2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus) ?_
  intro s3 hcl3 hpc3 hrun3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seq_wp_placed hcl3
    (new_addr_into_boxed_wp_placed x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hcl4 hpc4 hrun4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine signalMessageNew_seq_wp_placed hcl4
    (new_sret_stores_wp_placed x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hcl5 hpc5 hrun5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine signalMessageNew_seq_noPanic_placed' hcl5
    (new_dealloc_rk_and_ct_wpp_placed_at hcm_le hcm_bnd h_dealloc x sp0 rkPtr ctCopyPtr pqCopyPtr
      hct_bound s5 hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus) ?_
  intro s6 hcl6 hpc6 hrun6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine signalMessageNew_seq_noPanic_placed' hcl6
    (new_dealloc_pq_and_epilogue_wpp_placed_at hle hbnd hst_entails h_dealloc x pqCap pqCopyPtr
      hpq_bound s6 hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6' (hlr_ls := hlr_ls))
    (by sep_focus) ?_
  intro sf _ hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  rw [hstep_eq]
  exact entails_of_sep_focus (by sep_focus)

theorem new_phase3_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec M A lim C.F)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPhase3Events x))
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A.repAlloc (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) computeMacStack)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret
            (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool lim (M.stepEvents (newPhase3Events x) st) sf ∗
          stackAt s0.sp signalMessageNewStack))
      Qp :=
  new_phase3_wpp_placed_at (hookStack := allocHookStack) (by decide) (by decide)
    (fun c => newFrameRest_entails_stackAt sp0 c s0) h_shim h_alloc h_dealloc h_mc hMac x
    serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap verW32 hver haddrCap hct_bound hpq_bound hfit s
    hcl hpc hrun hsp hsp0 hsp0_align hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29 htr (hlr_ls := hlr_ls)

theorem new_phase3_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (hMac : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecX M A lim C.F)))
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPhase3Events x))
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .lr) := by simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A.repAlloc (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A.repAlloc (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A.repAlloc rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A.repAlloc ctCopyPtr x.ciphertext ∗
       optPqBuf A.repAlloc pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool lim st s ∗
       stackAt (sp0 - 416#64) computeMacStackX)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A.repAlloc g x.ret
            (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool lim (M.stepEvents (newPhase3Events x) st) sf ∗
          stackAt s0.sp signalMessageNewStackX))
      Qp :=
  new_phase3_wpp_placed_at (hookStack := extHookStack) (by decide) (by decide)
    (fun c => newFrameRest_entails_stackAtX sp0 c s0) h_shim h_alloc h_dealloc h_mc hMac x
    serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap verW32 hver haddrCap hct_bound hpq_bound hfit s
    hcl hpc hrun hsp hsp0 hsp0_align hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29 htr (hlr_ls := hlr_ls)

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxesBudget
