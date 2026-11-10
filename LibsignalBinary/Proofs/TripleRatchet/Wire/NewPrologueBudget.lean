/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded `<SignalMessage>::new` Segment 1 (`+0x000 .. +0x100`)

Re-exports `NewPrologueBudgetAux` (`+0x000 → +0x07c / +0x0f0`) and proves relocatable
`[LibsignalPlacement]` budget-threaded segment lemmas for copying `ciphertext` and `pq_ratchet`
into temporary `Vec<u8>` buffers (`+0x07c → +0x100`) on Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsρ
   lsRustAllocSym lsRustNoAllocShimSym lsMemcpySym)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_63 blkPl_63 SignalMessageNewGhost TraceVRegsEq computeMacStack computeMacStackX
   framelessMemcpySpec mac_ls_externAt?_of_mem noAllocShimSpec
   optPqBuf signalMessageNew_vecU8Buf
   sp_add_32_add_8 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_sub_96_add_96)
open CryptoVerification.LibsignalTripleRatchet.NewPrologueCallees
  (entails_of_sep_focus satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget RustLayoutOk
   rustAllocEvents rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (rustCliAllocNoOomSpecWithStack rustCliAllocNoOomExternSpecWithStack
   subroutine_ok_allocNoOom_externWithStack_of_hookSat)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (newCtCopyEvents newPqCopyEvents newPrologueEvents newPostPrologueEvents
   new_prologue_wp_placed new_addr_and_rk_wpp_placed new_addr_and_rk_wpp_placed_x)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (framelessMemcpyBudgetSpec new_memcpy_placed_ok new_shim_placed_ok noAllocShimBudgetSpec)

export LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
  (newPrologueEvents newPostPrologueEvents
   new_prologue_wp_placed new_addr_and_rk_wpp_placed new_addr_and_rk_wpp_placed_x)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  sp_sub_96_add_96 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_add_32_add_8

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

private theorem bind_state {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : let sc := s; SepWPp prog ret sc P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  h

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

/-! ## `ciphertext` copy (`+0x07c / +0x0f0 → +0x0a8 / +0x0fc`) -/

theorem new_ct_copy_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A.repAlloc (BitVec.ofNat 64 x.ciphertext.length)
            (sm.readReg64 .x26) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29
  by_cases hct0 : BitVec.ofNat 64 x.ciphertext.length = 0#64
  · simp only [hct0, ↓reduceIte] at hpc
    have hct_empty : x.ciphertext.isEmpty = true := by
      have h := congrArg BitVec.toNat hct0
      simp only [BitVec.toNat_ofNat] at h
      exact List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero (by omega))
    have hevs0 : newCtCopyEvents x = [] := by simp [newCtCopyEvents, hct_empty]
    rw [hevs0, M.stepEvents_nil]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, *]
    · unfold signalMessageNew_vecU8Buf
      simp only [hct0, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right (by omega) ?_
      exact entails_of_sep_focus (by sep_focus)
  · simp only [hct0, ↓reduceIte] at hpc
    have hct_pos : 0 < x.ciphertext.length := by
      by_contra hle0; simp [Nat.le_zero.mp (Nat.not_lt.mp hle0)] at hct0
    have hct_nonempty : x.ciphertext.isEmpty = false := by
      cases hc : x.ciphertext <;> simp_all
    have hevs_ne : newCtCopyEvents x = rustAllocEvents x.ciphertext.length 1 := by
      simp [newCtCopyEvents, hct_nonempty]
    rw [hevs_ne] at hfit ⊢
    have hct_toNat : (BitVec.ofNat 64 x.ciphertext.length).toNat = x.ciphertext.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hct_msb : (BitVec.ofNat 64 x.ciphertext.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hct_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := subroutine_ok_allocNoOom_externWithStack_of_hookSat h_alloc
      (mac_ls_externAt?_of_mem (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)) hle hbnd
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_shim
    refine call_noPanic_extern (x := ())
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗ (x.ciphertextA ↦ₛ x.ciphertext) ∗
            A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
      hshim (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [s_shim, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_shim]
      simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    dsimp only [s_shim] at hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm1 => SepWPp.pure_elim fun htr1 => ?_
    dsimp only [s_shim] at hvm1 htr1 ⊢
    rw [← A.pool_transport lim st _ sf1 hvm1]
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (x.ciphertext.length, 1, st))
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗ (x.ciphertextA ↦ₛ x.ciphertext))
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsum : x.ciphertext.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : RustLayoutOk x.ciphertext.length 1 :=
        ⟨⟨hct_pos, hpow1, hsum⟩, by decide⟩
      dsimp only [rustCliAllocNoOomExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
        rustCliAllocNoOomSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    dsimp only [rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hoom, _halign_ptr⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    let st' := M.stepEvents (rustAllocEvents x.ciphertext.length 1) st
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_mc
    refine call_noPanic_extern (x := ⟨sf2.readReg64 .x0, x.ciphertextA, x.ciphertext⟩)
      (F := ((sp0 - 400#64) ↦₆₄ w400) ∗
            A.live (sf2.readReg64 .x0) x.ciphertext.length 1 ∗
            A.pool lim st' s_mc ∗ stackAt sf2.sp cmStack)
      hmemcpy (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
      (by simp only [s_mc, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_mc]
      simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hpc3 hrun3 hsp3 hcs3
    dsimp only [s_mc] at hsp3 hcs3
    rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm3 => SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
    dsimp only [s_mc] at hvm3 htr3 ⊢
    rw [← A.pool_transport lim st' _ sf3 hvm3]
    simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [s_mc, wp_norm, arm64_norm, *]
    · unfold signalMessageNew_vecU8Buf
      have h26_eq : sf3.readReg64 (Reg.gpr 26#5) = sf2.readReg64 (Reg.gpr 0#5) := by
        simp only [wp_norm, arm64_norm, *]
      simp only [hct0, ↓reduceIte, h26_eq, hsp2, A.repAlloc_live_norm, st', wp_norm, arm64_norm]
      refine Entails.pure_right ⟨by omega, hoom⟩ ?_
      exact entails_of_sep_focus (by sep_focus)

theorem new_ct_copy_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A.repAlloc (BitVec.ofNat 64 x.ciphertext.length)
            (sm.readReg64 .x26) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_ct_copy_wpp_placed_at (cmStack := computeMacStack) (by decide) (by decide)
    h_shim h_alloc h_mc x sp0 rkPtr w400 hct_bound hfit s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29

theorem new_ct_copy_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr w400 : BitVec 64)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hfit : FitsEvents M lim st (newCtCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64)
      s
      (((sp0 - 400#64) ↦₆₄ w400) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          signalMessageNew_vecU8Buf A.repAlloc (BitVec.ofNat 64 x.ciphertext.length)
            (sm.readReg64 .x26) x.ciphertext ∗
          A.pool lim (M.stepEvents (newCtCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_ct_copy_wpp_placed_at (cmStack := computeMacStackX) (by decide) (by decide)
    h_shim h_alloc h_mc x sp0 rkPtr w400 hct_bound hfit s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hx29

/-! ## `pq_ratchet` copy (`+0x0a8 / +0x0fc → +0x100`) -/

theorem new_pq_copy_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {cmStack : Nat} {Qp : State → SepProp → Prop}
    (hle : allocHookStack ≤ cmStack := by decide)
    (hbnd : cmStack ≤ 2 ^ 64 := by decide)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A.repAlloc (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29
  by_cases hpq0 : BitVec.ofNat 64 x.pqRatchet.length = 0#64
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_empty : x.pqRatchet.isEmpty = true := by
      have h := congrArg BitVec.toNat hpq0
      simp only [BitVec.toNat_ofNat] at h
      exact List.isEmpty_iff.mpr (List.eq_nil_of_length_eq_zero (by omega))
    have hevs0 : newPqCopyEvents x = [] := by simp [newPqCopyEvents, hpq_empty]
    rw [hevs0, M.stepEvents_nil]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 256#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, *]
    · unfold optPqBuf
      simp only [hpq_empty, ↓reduceIte, sepConj_emp, arm64_norm]
      refine Entails.pure_right rfl ?_
      exact entails_of_sep_focus (by sep_focus)
  · simp only [hpq0, ↓reduceIte] at hpc
    have hpq_pos : 0 < x.pqRatchet.length := by
      by_contra hle0; simp [Nat.le_zero.mp (Nat.not_lt.mp hle0)] at hpq0
    have hpq_nonempty : x.pqRatchet.isEmpty = false := by
      cases hp : x.pqRatchet <;> simp_all
    have hevs_ne : newPqCopyEvents x = rustAllocEvents x.pqRatchet.length 1 := by
      simp [newPqCopyEvents, hpq_nonempty]
    rw [hevs_ne] at hfit ⊢
    have hpq_toNat : (BitVec.ofNat 64 x.pqRatchet.length).toNat = x.pqRatchet.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hpq_msb : (BitVec.ofNat 64 x.pqRatchet.length).getLsbD 63 = false := by
      rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, hpq_toNat]
      exact Nat.testBit_lt_two_pow (by omega)
    have hshim := new_shim_placed_ok h_shim (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    have halloc := subroutine_ok_allocNoOom_externWithStack_of_hookSat h_alloc
      (mac_ls_externAt?_of_mem (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)) hle hbnd
    have hmemcpy := new_memcpy_placed_ok h_mc (prog := (blkPC_63).rebase (blkPl_63).base H) (i := 63)
    apply SepWPp.of_sepWP (mid := lsρ lsRustNoAllocShimSym)
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_shim
    refine call_noPanic_extern (x := ())
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
            A.pool lim st s_shim ∗ stackAt (sp0 - 416#64) cmStack)
      hshim (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, wp_norm, arm64_norm, *])
      (by simp only [s_shim, State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [s_shim, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_shim]
      simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hpc1 hrun1 hsp1 hcs1
    dsimp only [s_shim] at hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [noAllocShimBudgetSpec, withVmPreserved, noAllocShimSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm1 => SepWPp.pure_elim fun htr1 => ?_
    dsimp only [s_shim] at hvm1 htr1 ⊢
    rw [← A.pool_transport lim st _ sf1 hvm1]
    simp only [wp_norm, arm64_norm] at htr1
    apply SepWPp.of_sepWP (mid := lsρ lsRustAllocSym)
    wp_steps_sync_pool (lsρ lsRustAllocSym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine call_noPanic_extern (x := (x.pqRatchet.length, 1, st))
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗ (x.pqRatchetA ↦ₛ x.pqRatchet))
      halloc (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hsum : x.pqRatchet.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : RustLayoutOk x.pqRatchet.length 1 :=
        ⟨⟨hpq_pos, hpow1, hsum⟩, by decide⟩
      dsimp only [rustCliAllocNoOomExternSpecWithStack,
        _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
        rustCliAllocNoOomSpecWithStack]
      simp (config := { decide := true }) only [sepConj_assoc, wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    dsimp only [rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr2, hoom, _halign_ptr⟩ => ?_
    have hoom_beq : (sf2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [wp_norm, arm64_norm, htr1] at htr2 hoom hoom_beq
    let st' := M.stepEvents (rustAllocEvents x.pqRatchet.length 1) st
    apply SepWPp.of_sepWP (mid := lsρ lsMemcpySym)
    wp_steps_sync_pool (lsρ lsMemcpySym)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    refine bind_state ?_
    intro s_mc
    refine call_noPanic_extern (x := ⟨sf2.readReg64 .x0, x.pqRatchetA, x.pqRatchet⟩)
      (F := ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
            A.live (sf2.readReg64 .x0) x.pqRatchet.length 1 ∗
            A.pool lim st' s_mc ∗ stackAt sf2.sp cmStack)
      hmemcpy (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, wp_norm, arm64_norm, *])
      (by simp only [s_mc, State.spAligned, wp_norm, arm64_norm, hsp2, hsp0_align])
      (by simp only [s_mc, arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      dsimp only [s_mc]
      simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf3 hpc3 hrun3 hsp3 hcs3
    dsimp only [s_mc] at hsp3 hcs3
    rcases hcs3 with ⟨h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3, h27_3, h28_3, hfp_3⟩
    simp only [wp_norm, arm64_norm, *] at hsp3 h19_3 h20_3 h21_3 h22_3 h23_3 h24_3 h25_3 h26_3 h27_3 h28_3 hfp_3
    simp only [framelessMemcpyBudgetSpec, withVmPreserved, framelessMemcpySpec, sepConj_assoc]
    refine SepWPp.pure_elim fun hvm3 => SepWPp.pure_elim fun ⟨hx0_3, htr3⟩ => ?_
    dsimp only [s_mc] at hvm3 htr3 ⊢
    rw [← A.pool_transport lim st' _ sf3 hvm3]
    simp only [wp_norm, arm64_norm, htr2] at hx0_3 htr3
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool ((blkPl_63).base + 256#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [s_mc, wp_norm, arm64_norm, *]
    · unfold optPqBuf
      have h25_eq : sf3.readReg64 (Reg.gpr 25#5) = sf2.readReg64 (Reg.gpr 0#5) := by
        simp only [wp_norm, arm64_norm, *]
      simp only [hpq_nonempty, Bool.false_eq_true, ↓reduceIte, hsp2,
        h25_eq, A.repAlloc_live_norm, st', wp_norm, arm64_norm]
      refine Entails.pure_right ⟨hpq_pos, by omega, hoom⟩ ?_
      exact entails_of_sep_focus (by sep_focus)

theorem new_pq_copy_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A.repAlloc (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_pq_copy_wpp_placed_at (cmStack := computeMacStack) (by decide) (by decide)
    h_shim h_alloc h_mc x sp0 rkPtr ctCopyPtr hpq_bound hfit s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29

theorem new_pq_copy_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_mc : HookSat H lsMemcpySym framelessMemcpyBudgetSpec)
    (x : SignalMessageNewGhost) (sp0 rkPtr ctCopyPtr : BitVec 64)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (hfit : FitsEvents M lim st (newPqCopyEvents x))
    (s : State)
    (hpc : s.pc =
      (if BitVec.ofNat 64 x.pqRatchet.length = 0#64 then
        (blkPl_63).base + 252#64
       else
        (blkPl_63).base + 168#64))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx26 : s.readReg64 .x26 = ctCopyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx28 : s.readReg64 .x28 = rkPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      ((blkPl_63).base + 256#64)
      s
      (((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x26 = ctCopyPtr ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x28 = rkPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          optPqBuf A.repAlloc (sm.readReg64 .x9) (sm.readReg64 .x25) x.pqRatchet ∗
          A.pool lim (M.stepEvents (newPqCopyEvents x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_pq_copy_wpp_placed_at (cmStack := computeMacStackX) (by decide) (by decide)
    h_shim h_alloc h_mc x sp0 rkPtr ctCopyPtr hpq_bound hfit s hpc hrun hsp hsp_align
    hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27 hx28 hx29

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudget
