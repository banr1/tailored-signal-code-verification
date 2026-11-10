/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudget
import ProofLib.SepLogic.WPp

/-!
# `HookSat`-Backed `VmPreserved` `StoreKit.Over.MatchCallee` Proofs (`MatchCalleeBudgetSat`)

Additive `HookSat H lsBlackBoxU8Sym blackBoxSpecSat` sibling of
`LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudget`.

Threads 2 of the 8 scratch cells in `cells (sp - 1248) 8` (`16` B at `[sp - 1200, sp - 1184)`,
i.e. `stackAt (sp - 1184) 16`) across `subtle::black_box::<u8>` calls before the `+236` (`+0xec`)
`Map::next` epilogue, keeping every raw and record-level theorem conclusion token-identical to
`MatchCalleeBudget`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudgetSat

open Arm64 Arm64.Obj ProofLib ProofLib.GenPlacedFetches SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkLib_eq_50 blkPC_50 blkPl_50
   extract_withLsCodeLoaded lsBlackBoxU8Sym ls_externAt?_of_mem ls_subroutine_ok_cl_of_plain
   lsmpl lsρ sepWP_mono_lscl sepWP_seq_lscl withLsCl withLsCodeLoaded)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (promoteSavedRegs)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (PromoteKeyMissRawGhost PromoteLenMissRawGhost PromoteMissGhost PromoteVerMissRawGhost
   aliceBufOverAt aliceBufOverAt_expose_33 ctBytesEqAcc ctBytesEqAcc_true_of_ne ofNat_len_ne_33
   outRegion16_split_over promoteMatchingSessionMissStack promoteMissStackCells sessionRecordAt_expose_miss
   sessionRecordAt_miss_facts sessionRecordMissPromoteFieldsAt sessionRecordMissRestAt
   stackAt_promoteMissStack_eq)
open CryptoVerification.E2E.Pqxdh.ResponderStore (mapIterNextEmptySpec)
open CryptoVerification.LibsignalPublicApiRepr (sessionRecordAt)
open CryptoVerification.LibsignalTripleRatchet (blackBoxSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpec16 blackBoxSpecSat)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudget
  (map_iter_next_empty_placed_ok promote_matching_session_ver_miss_raw_placed_ok)
open LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget
  (promoteMatchingSessionKeyMissRawSpec promoteMatchingSessionLenMissRawSpec
   promoteMatchingSessionMissSpec promoteMatchingSessionRecordOverSpec
   promoteMatchingSessionVerMissRawSpec)

set_option maxRecDepth 200000

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "cells_unfold_over" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub])

/-! ## 1. Local Normalization, Stack Split, & `HookSat` `black_box` Stepping -/

private theorem cond_eq_adds64_one_false_over {c : BitVec 64} (hc : c ≠ 0xffffffffffffffff#64) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]; intro heq; apply hc; bv_omega

private theorem cond_ne_subs64_one_over {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]; intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat; omega

private theorem ofNat64_succ_sub_one_over (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align_over (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align_over (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align_over (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self_over (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self_over (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self_over (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]
@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_setWidth32_byte_over (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).setWidth 32 = v.zeroExtend 32 := by bv_omega
@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_extractLsb32_byte_over (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).extractLsb' 0 32 = v.zeroExtend 32 := by bv_slice
@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_setWidth32_over (sessVer : BitVec 32) :
    BitVec.setWidth 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]; by_cases h : sessVer = 0#32 <;> simp [h]
@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_extractLsb32_over (sessVer : BitVec 32) :
    BitVec.extractLsb' 0 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]; by_cases h : sessVer = 0#32
  · subst h; decide
  · simp only [beq_iff_eq, h, ↓reduceIte]; bv_slice
@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_over (a b : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 b) = (a != b) := by
  by_cases h : a = b
  · subst h; simp [bne]
  · have h32 : BitVec.setWidth 32 a ≠ BitVec.setWidth 32 b := fun heq => h (by bv_omega)
    rw [bne_iff_ne.mpr h32, bne_iff_ne.mpr h]
@[local simp, local wp_norm, local arm64_norm]
private theorem ite_bne_byte_0_1_over (a b : BitVec 8) :
    (if (a != b) = true then 0#64 else 1#64) = if (a == b) = true then 1#64 else 0#64 := by
  cases h : a == b <;> simp [bne, h]
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0_over (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0_over (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32_over (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8_over (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem zeroExtend64_ite_1_0_8_over (c : Bool) :
    BitVec.zeroExtend 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0_over (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by cases c1 <;> cases c2 <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0_over (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by cases c1 <;> cases c2 <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0_over (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem extractLsb32_ite_1_0_over (c : Bool) :
    BitVec.extractLsb' 0 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0_8_over (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#8 else 0#8) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_and64_over (a b : BitVec 64) :
    BitVec.setWidth 32 (a &&& b) = BitVec.setWidth 32 a &&& BitVec.setWidth 32 b := by bv_robdd
@[local simp, local wp_norm, local arm64_norm]
private theorem and32_one_ite_1_0_over (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

private theorem cells_96_12_eq_over (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗ ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
       ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗ ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
       ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗ ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
       ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗ ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
       ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗ ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
       ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗ ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

private theorem cells_1184_split_2 (sp : BitVec 64) :
    cells (sp - 1184#64) 10 =
      (∃∗ w4a0 : BitVec 64, (sp - 1184#64) ↦₆₄ w4a0) ∗
      (∃∗ w470 : BitVec 64, (sp - 1136#64) ↦₆₄ w470) ∗
      (cells (sp - 1176#64) 5 ∗ cells (sp - 1128#64) 3) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  simp only [← sepExists_sepConj_left, sepConj_emp]
  rw [hstep 1184#64 1176#64 rfl, hstep 1176#64 1168#64 rfl, hstep 1168#64 1160#64 rfl,
      hstep 1160#64 1152#64 rfl, hstep 1152#64 1144#64 rfl, hstep 1144#64 1136#64 rfl,
      hstep 1136#64 1128#64 rfl, hstep 1128#64 1120#64 rfl, hstep 1120#64 1112#64 rfl]
  sep_ac_rfl

private theorem cells_1184_merge_2 (sp v0 v6 : BitVec 64) :
    ((sp - 1184#64) ↦₆₄ v0) ∗ ((sp - 1136#64) ↦₆₄ v6) ∗
      (cells (sp - 1176#64) 5 ∗ cells (sp - 1128#64) 3) ⊢
      cells (sp - 1184#64) 10 := by
  rw [cells_1184_split_2 sp]
  exact sepConj_mono (Entails.sepExists_right v0 (Entails.refl _))
    (sepConj_mono_left (Entails.sepExists_right v6 (Entails.refl _)))

/-- Splits `cells (sp - 1248) 8` (`64` B) into `cells (sp - 1248) 6` (`48` B) plus
`stackAt (sp - 1184) 16` (`16` B at `[sp - 1200, sp - 1184)`) for `blackBoxSpecSat`. -/
private theorem cells_1248_8_eq_stack16 (sp : BitVec 64) :
    cells (sp - 1248#64) 8 =
      cells (sp - 1248#64) 6 ∗ stackAt (sp - 1184#64) 16 := by
  rw [← ProofLib.memRegion_cells (sp - 1248#64) 8 (by decide),
      ← ProofLib.memRegion_cells (sp - 1248#64) 6 (by decide)]
  exact ProofLib.memRegion_split' (b := sp - 1248#64) (b' := (sp - 1184#64) - 16#64)
    (N := 64) (n := 48) (k := 16) (by decide) (by bv_omega) (by decide)

private theorem black_box_placed_ok_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym)
      blackBoxSpecSat := by
  rcases h_bb with ⟨f_bb, hfH, hfOk⟩
  exact subroutine_ok_of_hookOk
    ((ls_externAt?_of_mem (prog := (blkPC_50).rebase (blkPl_50).base H)
      (sym := lsBlackBoxU8Sym)).trans hfH)
    hfOk

private theorem call_blackBox_sat_over [LibsignalPlacement] {H : LibsignalHooks}
    {target_pc ret_pc sp0 : BitVec 64} {s0 s_cur : State} {v : BitVec 64}
    {P F : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hvm0 : VmPreserved s0 s_cur)
    (hpc : s_cur.pc = lsρ lsBlackBoxU8Sym)
    (hrun : s_cur.status = .Running)
    (hsp : s_cur.sp = sp0)
    (hlr : s_cur.readReg64 (Reg.gpr 30#5) = ret_pc)
    (hx0 : s_cur.readReg64 (Reg.gpr 0#5) = v)
    (hP : P = stackAt sp0 16 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      VmPreserved s0 sf →
      sf.trace = s_cur.trace →
      sf.sp = sp0 →
      sf.readReg64 (Reg.gpr 0#5) = (v.setWidth 8).zeroExtend 64 →
      CalleeSavedPreserved s_cur sf →
      SepWP ((blkPC_50).rebase (blkPl_50).base H) target_pc sf P post) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) target_pc s_cur P post := by
  have hsp_al : s_cur.spAligned = true := by
    unfold State.spAligned
    rwa [hsp]
  rw [hP]
  refine SepWP.call_subroutine_frame hbb (x := v) (F := F)
    hpc hrun hsp_al hlr
    (fun R hm => by
      rw [sepConj_assoc] at hm
      dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec]
      simp only [hsp, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hx0, hm⟩)
    (fun _ _ _ hpost => not_satisfies_false_sepConj (by
      simpa only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec] using hpost))
    (fun _ _ _ _ hpost => not_satisfies_false_sepConj (by
      simpa only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
        CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec] using hpost))
    ?_
  intro sf hret_pc hret_run hsp_eq hcs
  dsimp only [blackBoxSpecSat, withVmPreserved, blackBoxSpec16,
    CryptoVerification.LibsignalTripleRatchet.withStack, blackBoxSpec]
  simp only [hsp, sepConj_assoc]
  apply SepWP.pure_elim
  intro hvm_bb
  apply SepWP.pure_elim
  rintro ⟨hx0_sf, htr_sf⟩
  rw [← hP]
  exact hnext sf hret_pc hret_run (hvm0.trans hvm_bb) htr_sf (hsp_eq.trans hsp) hx0_sf hcs

/-! ## 2. Shared Epilogue from `+236` (`+0xec`) with `calleeSavedVRegs` -/

private theorem sepWP_add_lscl {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Q : State → SepProp → Prop} {R : State → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf => Q sf Pf ∧ R sf)) :
    SepWP prog tgt s P (fun sf Pf => Q sf Pf ∧ LibsignalCodeLoaded pl sf.mem ∧ R sf) :=
  sepWP_mono_lscl hcl h (fun _ _ _ _ hcl1 ⟨hq, hr⟩ => ⟨hq, hcl1, hr⟩)

private theorem sepWP_add_lscl_vm {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Q : State → SepProp → Prop} {R : State → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog tgt s P (fun sf Pf => VmPreserved s sf ∧ Q sf Pf ∧ R sf)) :
    SepWP prog tgt s P (fun sf Pf => Q sf Pf ∧ LibsignalCodeLoaded pl sf.mem ∧ VmPreserved s sf ∧ R sf) :=
  sepWP_mono_lscl hcl h (fun _ _ _ _ hcl1 ⟨hvm, hq, hr⟩ => ⟨hq, hcl1, hvm, hr⟩)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
private theorem promote_miss_from_ec_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (s0 s2 : State) (recPtr prevPtr outPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (hvm02 : VmPreserved s0 s2)
    (hpc : s2.pc = (blkPl_50).base + 236#64)
    (hrun : s2.status = .Running)
    (hsp_align : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : s2.trace = s0.trace)
    (hsp : s2.sp = s0.sp - 1184#64)
    (hx0 : s2.readReg64 .x0 = recPtr)
    (hx23 : s2.readReg64 .x23 = outPtr)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s0) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) (s0.readReg64 .x30) s2
      (((recPtr + 8#64) ↦₆₄ prevPtr) ∗
       ((recPtr + 16#64) ↦₆₄ 0#64) ∗
       (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
       (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
       cells (s0.sp - 1248#64) 8 ∗
       cells (s0.sp - 1184#64) 10 ∗
       (∃∗ w2e0 : BitVec 64, (s0.sp - 448#64) ↦₆₄ w2e0) ∗
       promoteSavedRegs s0)
      (fun sf Pf =>
        (Pf ⊢
          ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
          ((recPtr + 16#64) ↦₆₄ 0#64) ∗
          (outPtr ↦₆₄ 0#64) ∗
          ((outPtr + 8#64) ↦₈ 0#8) ∗
          promoteMissStackCells s0.sp) ∧
        VmPreserved s0 sf ∧
        sf.trace = s0.trace ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) := by
  unfold promoteSavedRegs
  have hiter := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_50).rebase (blkPl_50).base H) (entry := lsmpl.base 83)
    (map_iter_next_empty_placed_ok H)
  cells_unfold_over
  simp only [withLsCl, withVmPreserved, mapIterNextEmptySpec, cells, sepConj_emp,
    sepExists_sepConj_right, bv_sub_add_lit, BitVec.add_assoc, BitVec.reduceAdd,
    BitVec.reduceSub] at hiter
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = recPtr := hx0
  have hx23' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  wp_pull_exists
  apply sepWP_seq_lscl hcl (mid := lsmpl.base 83)
  apply sepWP_seg_ls_vm (Q := (blkPC_50).rebase (blkPl_50).base (hooksException H))
    blkLib_eq_50 (mid := lsmpl.base 83)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  have hvm23 := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, prevPtr)
  have hvm24 : VmPreserved s2 sf := hvm23.trans ‹_›
  refine SepWP.mono (post := fun sfin Pf =>
      VmPreserved sf sfin ∧
      (Pf ⊢
        ((recPtr + 8#64) ↦₆₄ prevPtr) ∗
        ((recPtr + 16#64) ↦₆₄ 0#64) ∗
        (outPtr ↦₆₄ 0#64) ∗
        ((outPtr + 8#64) ↦₈ 0#8) ∗
        promoteMissStackCells s0.sp) ∧
      sfin.trace = s0.trace ∧
      sfin.sp = s0.sp ∧
      CalleeSavedPreserved s0 sfin) ?_ ?_
  · by_vm_steps (
      wp_steps
      refine SepWP.done (by simp only [hsp, wp_norm, arm64_norm])
        (by simp only [hrun_sf, wp_norm, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm],
         ?_,
         by simp only [htr, hpost, wp_norm, arm64_norm],
         by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
         ⟨by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [hsp, hsp_sf, wp_norm, arm64_norm],
          by simp only [CalleeSavedVRegsPreserved, wp_norm, arm64_norm] at hvregs_1 ⊢
             exact hvregs_1.trans hvregs⟩⟩
      unfold promoteMissStackCells
      cells_unfold_over
      sep_frame)
  · intro sfin _ _ _ ⟨hvm4f, hentf, htrf, hspf, hcsf⟩
    exact ⟨hentf, hvm02.trans (hvm24.trans hvm4f), htrf, hspf, hcsf⟩

/-! ## 3. Inductive Constant-Time Byte-Comparison Loop (`VmPreserved` + `stackAt s.sp 16`) -/

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_last_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (k0 a0 : BitVec 8) (acc : Bool)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = 1#64)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 180#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp 16)
      (fun sf Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp 16) ∧
        VmPreserved s sf ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.readReg64 .x26 = recPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 1#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps
  refine call_blackBox_sat_over (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
    (v := if (k0 == a0) = true then 1#64 else 0#64)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun s1 hpc1 hrun1 hvm1 htr1 hsp1 hx0_1 hcs1 => ?_
  have htr1' : s1.trace = s.trace := htr1.trans (by simp only [wp_norm, arm64_norm])
  have hx0_1' : s1.readReg64 (Reg.gpr 0#5) = if (k0 == a0) = true then 1#64 else 0#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_1
  have hx21_1 : s1.readReg64 (Reg.gpr 21#5) = 1#64 :=
    hcs1.2.2.1.trans (by simp only [hx21', wp_norm, arm64_norm])
  have hx23_1 : s1.readReg64 (Reg.gpr 23#5) = outPtr :=
    hcs1.2.2.2.2.1.trans (by simp only [hx23', wp_norm, arm64_norm])
  have hx25_1 : s1.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 :=
    hcs1.2.2.2.2.2.2.1.trans (by simp only [hx25', wp_norm, arm64_norm])
  have hx26_1 : s1.readReg64 (Reg.gpr 26#5) = recPtr :=
    hcs1.2.2.2.2.2.2.2.1.trans (by simp only [hx26', wp_norm, arm64_norm])
  have hv1 : calleeSavedVRegs s1 = calleeSavedVRegs s :=
    hcs1.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])
  clear hcs1 htr1 hx0_1
  wp_steps
  refine call_blackBox_sat_over (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
    (v := if ((k0 == a0) && acc) = true then 1#64 else 0#64)
    (hvm1.trans (by simp only [wp_norm, arm64_norm]))
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm])
    (by simp only [hrun1, wp_norm, arm64_norm])
    (by simp only [hsp1, wp_norm, arm64_norm])
    (by simp only [hpc1, hx21_1, wp_norm, arm64_norm]; rfl)
    (by simp only [hx0_1', hx21_1, hx25_1, wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun sf hpcf hrunf hvmf htrf hspf hx0_f hcsf => ?_
  have htrf' : sf.trace = s.trace :=
    (htrf.trans (by simp only [wp_norm, arm64_norm])).trans htr1'
  have hx0_f' : sf.readReg64 .x0 = if ((k0 == a0) && acc) = true then 1#64 else 0#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_f
  have hx23_f : sf.readReg64 .x23 = outPtr :=
    hcsf.2.2.2.2.1.trans (by simp only [hx23_1, wp_norm, arm64_norm])
  have hx26_f : sf.readReg64 .x26 = recPtr :=
    hcsf.2.2.2.2.2.2.2.1.trans (by simp only [hx26_1, wp_norm, arm64_norm])
  have hvf : calleeSavedVRegs sf = calleeSavedVRegs s :=
    (hcsf.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])).trans hv1
  exact SepWP.done (by simp only [hpc1, hpcf, hx21_1, wp_norm, arm64_norm]) hrunf
    ⟨rfl, hvmf, htrf', hspf, hx0_f', hx23_f, hx26_f, hvf⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_step_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (k0 a0 : BitVec 8) (acc : Bool) (m : Nat) (hm_pos : 0 < m) (hm_lt : m + 1 < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (m + 1))
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 128#64) s
      ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp 16)
      (fun s1 Pf =>
        Pf = ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp 16) ∧
        VmPreserved s s1 ∧
        s1.trace = s.trace ∧
        s1.sp = s.sp ∧
        s1.readReg64 .x19 = alicePtr + 1#64 ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 m ∧
        s1.readReg64 .x22 = serPtr + 1#64 ∧
        s1.readReg64 .x23 = outPtr ∧
        s1.readReg64 .x25 = (if ((k0 == a0) && acc) = true then 1#64 else 0#64) ∧
        s1.readReg64 .x26 = recPtr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hgt : 1 < m + 1 := by omega
  have hbr := cond_ne_subs64_one_over hgt hm_lt
  have hsub1 : BitVec.ofNat 64 (m + 1) - 1#64 = BitVec.ofNat 64 m := ofNat64_succ_sub_one_over m
  have hx19' : s.readReg64 (Reg.gpr 19#5) = alicePtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = serPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = outPtr := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = recPtr := hx26
  wp_steps
  refine call_blackBox_sat_over (s0 := s) hbb hsp_align
    (F := (serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0))
    (v := if (k0 == a0) = true then 1#64 else 0#64)
    (by simp only [wp_norm, arm64_norm])
    (by simp only [hpc, hx21', hbr, wp_norm, arm64_norm])
    (by simp only [hrun, wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm])
    (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm])
    (by sep_ac_rfl)
    fun sb hpcb hrunb hvmb htrb hspb hx0_b hcsb => ?_
  have htrb' : sb.trace = s.trace := htrb.trans (by simp only [wp_norm, arm64_norm])
  have hx0_b' : sb.readReg64 (Reg.gpr 0#5) = if (k0 == a0) = true then 1#64 else 0#64 := by
    simpa only [wp_norm, arm64_norm] using hx0_b
  have hx19_b : sb.readReg64 (Reg.gpr 19#5) = alicePtr + 1#64 :=
    hcsb.1.trans (by simp only [wp_norm, arm64_norm])
  have hx21_b : sb.readReg64 (Reg.gpr 21#5) = BitVec.ofNat 64 (m + 1) :=
    hcsb.2.2.1.trans (by simp only [hx21', wp_norm, arm64_norm])
  have hx22_b : sb.readReg64 (Reg.gpr 22#5) = serPtr + 1#64 :=
    hcsb.2.2.2.1.trans (by simp only [wp_norm, arm64_norm])
  have hx23_b : sb.readReg64 (Reg.gpr 23#5) = outPtr :=
    hcsb.2.2.2.2.1.trans (by simp only [hx23', wp_norm, arm64_norm])
  have hx25_b : sb.readReg64 (Reg.gpr 25#5) = if acc = true then 1#64 else 0#64 :=
    hcsb.2.2.2.2.2.2.1.trans (by simp only [hx25', wp_norm, arm64_norm])
  have hx26_b : sb.readReg64 (Reg.gpr 26#5) = recPtr :=
    hcsb.2.2.2.2.2.2.2.1.trans (by simp only [hx26', wp_norm, arm64_norm])
  have hvb : calleeSavedVRegs sb = calleeSavedVRegs s :=
    hcsb.2.2.2.2.2.2.2.2.2.2.2.trans (by simp only [wp_norm, arm64_norm])
  clear hcsb htrb hx0_b
  wp_steps
  refine SepWP.done (by simp only [hpc, hpcb, hx21_b, hbr, wp_norm, arm64_norm])
    (by simp only [hrunb, wp_norm, arm64_norm])
    ⟨rfl, hvmb.trans (by simp only [wp_norm, arm64_norm]),
     by simp only [htrb', wp_norm, arm64_norm],
     by simp only [hspb, wp_norm, arm64_norm],
     by simp only [hx19_b, wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm, hx21_b, hsub1],
     by simp only [hx22_b, wp_norm, arm64_norm],
     by simp only [hx23_b, wp_norm, arm64_norm],
     by simp only [hx0_b', hx25_b, wp_norm, arm64_norm],
     by simp only [hx26_b, wp_norm, arm64_norm],
     by simp only [hvb, wp_norm, arm64_norm]⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem promote_ct_loop_gen_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (hbb : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpecSat)
    (ks as_ : List (BitVec 8)) (acc : Bool)
    (hlen : ks.length = as_.length) (hne : ks ≠ []) (hlt : ks.length < 2 ^ 64)
    (recPtr serPtr alicePtr outPtr : BitVec 64) (s : State)
    (hpc : s.pc = (blkPl_50).base + 128#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = alicePtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 ks.length)
    (hx22 : s.readReg64 .x22 = serPtr)
    (hx23 : s.readReg64 .x23 = outPtr)
    (hx25 : s.readReg64 .x25 = if acc = true then 1#64 else 0#64)
    (hx26 : s.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 180#64) s
      ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp 16)
      (fun sf Pf =>
        Pf = ((serPtr ↦ₛ ks) ∗ (alicePtr ↦ₛ as_) ∗ stackAt s.sp 16) ∧
        VmPreserved s sf ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x0 = (if ctBytesEqAcc ks as_ acc = true then 1#64 else 0#64) ∧
        sf.readReg64 .x23 = outPtr ∧
        sf.readReg64 .x26 = recPtr ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  induction ks generalizing as_ acc serPtr alicePtr s with
  | nil => exact absurd rfl hne
  | cons k0 krest ih =>
    cases as_ with
    | nil => simp at hlen
    | cons a0 arest =>
      have hlen' : krest.length = arest.length := by simpa using hlen
      cases krest with
      | nil =>
        cases arest with
        | nil =>
          dsimp only [List.length_cons, List.length_nil, ctBytesEqAcc] at hx21 ⊢
          have hpre_eq : ((serPtr ↦ₛ [k0]) ∗ (alicePtr ↦ₛ [a0]) ∗ stackAt s.sp 16) =
              ((serPtr ↦₈ k0) ∗ (alicePtr ↦₈ a0) ∗ stackAt s.sp 16) := by
            rw [pointsToBytes_cons, pointsToBytes_nil, pointsToBytes_cons, pointsToBytes_nil,
              sepConj_emp, sepConj_emp]
          rw [hpre_eq]
          exact promote_ct_loop_last_placed_wp hbb k0 a0 acc recPtr serPtr alicePtr outPtr s
            hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25 hx26
        | cons _ _ => simp at hlen'
      | cons k1 krest' =>
        cases arest with
        | nil => simp at hlen'
        | cons a1 arest' =>
          have hm_pos : 0 < (k1 :: krest').length := by simp
          have hm_lt : (k1 :: krest').length + 1 < 2 ^ 64 := by simpa using hlt
          have hlt' : (k1 :: krest').length < 2 ^ 64 := by omega
          dsimp only [List.length_cons] at hx21
          conv =>
            arg 4
            rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
            simp only [sepConj_assoc]
          refine SepWP.bind_seq_readOnly
            (promote_ct_loop_step_placed_wp hbb k0 a0 acc (k1 :: krest').length hm_pos hm_lt
              recPtr serPtr alicePtr outPtr s hpc hrun hsp_align hx19 hx21 hx22 hx23 hx25 hx26)
            (by sep_focus)
            fun s1 hpc1 hrun1 ⟨hvm1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩ => ?_
          have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := by
            rwa [hsp1]
          have hih := ih (a1 :: arest') ((k0 == a0) && acc) hlen' (by simp) hlt'
            (serPtr + 1#64) (alicePtr + 1#64) s1 hpc1 hrun1 hsp_align1
            hx19_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1
          rw [hsp1] at hih
          refine SepWP.bind_seq_readOnly hih (by sep_focus)
            fun sf hpcf hrunf ⟨hvmf, htrf, hspf, hx0_f, hx23_f, hx26_f, hv_f⟩ => ?_
          refine SepWP.done hpcf hrunf
            ⟨?_, hvm1.trans hvmf, htrf.trans htr1, hspf,
             hx0_f, hx23_f, hx26_f, hv_f.trans hv1⟩
          rw [pointsToBytes_cons serPtr, pointsToBytes_cons alicePtr]
          sep_ac_rfl

/-! ## 4. Raw & Record-Level Relocatable `[LibsignalPlacement]` Miss Theorems (`_sat`) -/

set_option linter.unusedSimpArgs false in
private theorem promote_b4_to_ec_placed_wp [LibsignalPlacement] {H : LibsignalHooks}
    (recPtr outPtr : BitVec 64) (s2 : State)
    (hcl2 : LibsignalCodeLoaded lsmpl s2.mem)
    (hpc2 : s2.pc = (blkPl_50).base + 180#64)
    (hrun2 : s2.status = .Running)
    (hx0_2 : s2.readReg64 .x0 = 0#64)
    (hx23_2 : s2.readReg64 .x23 = outPtr)
    (hx26_2 : s2.readReg64 .x26 = recPtr) :
    SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 236#64) s2 emp
      (fun s3 P3 =>
        P3 = emp ∧ LibsignalCodeLoaded lsmpl s3.mem ∧ VmPreserved s2 s3 ∧
        s3.trace = s2.trace ∧ s3.sp = s2.sp ∧
        s3.readReg64 .x0 = recPtr ∧ s3.readReg64 .x23 = outPtr ∧ s3.vregs = s2.vregs) := by
  apply sepWP_add_lscl hcl2
  have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx23_2' : s2.readReg64 (Reg.gpr 23#5) = outPtr := hx23_2
  have hx26_2' : s2.readReg64 (Reg.gpr 26#5) = recPtr := hx26_2
  wp_steps
  exact SepWP.done (by simp only [hpc2, hx0_2', wp_norm, arm64_norm])
    (by simp only [hrun2, wp_norm, arm64_norm])
    ⟨rfl, by simp only [wp_norm, arm64_norm],
     by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
     by simp only [hx26_2', wp_norm, arm64_norm], by simp only [hx23_2', wp_norm, arm64_norm], rfl⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
/-- `HookSat` `black_box` sibling of `MatchCalleeBudget.promote_matching_session_len_miss_raw_placed_ok`. -/
theorem promote_matching_session_len_miss_raw_placed_ok_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionLenMissRawSpec) := by
  have hbb := black_box_placed_ok_sat h_bb
  clear h_bb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, abkLen, sessVer, msgVer, serPtr, outPtr⟩ R s0
      hpc hrun hpre hsp_align => ?_
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [promoteMatchingSessionLenMissRawSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpec,
    sessionRecordMissPromoteFieldsAt] at hpre'
  dsimp only [withLsCodeLoaded, promoteMatchingSessionLenMissRawSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpec,
    sessionRecordMissPromoteFieldsAt]
  refine ⟨_, hpre', ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hsp_align16 : (((s0.sp - 1184#64) &&& 15#64) == 0#64) = true := by
    rw [sp_sub_1184_align_over]; exact hsp_align'
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hlen_ne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hlne_b : (33#64 != abkLen) = true := bne_iff_ne.mpr (fun h33 => hlen_ne h33.symm)
  have hlne_b' : (abkLen != 33#64) = true := bne_iff_ne.mpr hlen_ne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1248_8_eq_stack16 s0.sp, cells_1184_split_2 s0.sp]
  have hp1a :
      SepWP ((blkPC_50).rebase (blkPl_50).base H) (lsρ lsBlackBoxU8Sym) s0
        (((recPtr + 24#64) ↦₆₄ curDiscr) ∗
         ((recPtr + 136#64) ↦₆₄ abkLen) ∗
         ((recPtr + 352#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
         cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 24#64) ↦₆₄ curDiscr) ∗ ((recPtr + 136#64) ↦₆₄ abkLen) ∗
            ((recPtr + 352#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          LibsignalCodeLoaded lsmpl s1.mem ∧
          VmPreserved s0 s1 ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x0 = 0#64 ∧ s1.readReg64 .x23 = outPtr ∧
          s1.readReg64 .x26 = recPtr ∧ s1.readReg64 .lr = (blkPl_50).base + 180#64 ∧
          s1.vregs = s0.vregs) := by
    apply sepWP_add_lscl_vm hcl0
    rw [cells_96_12_eq_over s0.sp]
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists
    by_vm_steps (
      wp_steps
      refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hlne_b, hlne_b', hx3', wp_norm, arm64_norm])
        (by simp only [hrun, wp_norm, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm],
         ?_,
         by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
         by simp only [wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm],
         by simp only [hx0', wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], rfl⟩
      unfold promoteSavedRegs
      sep_frame)
  apply SepWP.seq
  · exact SepWP.frame_auto hp1a
  · intro s1 _ hpc1 hrun1 ⟨hent1, hcl1, hvm1, htr1, hsp1, hx0_1, hx23_1, hx26_1, hlr1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hp1b :
        SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 180#64) s1
          (stackAt (s0.sp - 1184#64) 16)
          (fun s2 P2 =>
            P2 = stackAt (s0.sp - 1184#64) 16 ∧
            LibsignalCodeLoaded lsmpl s2.mem ∧ VmPreserved s1 s2 ∧
            s2.trace = s1.trace ∧ s2.sp = s1.sp ∧
            s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x23 = outPtr ∧
            s2.readReg64 .x26 = recPtr ∧ calleeSavedVRegs s2 = calleeSavedVRegs s1) := by
      apply sepWP_add_lscl hcl1
      refine call_blackBox_sat_over hbb hsp_align16 (F := emp) (v := 0#64)
        (VmPreserved.refl s1) hpc1 hrun1 hsp1 hlr1 hx0_1 (sepConj_emp _).symm
        fun s2 hpc2 hrun2 hvm2 htr2 hsp2 hx0_2 hcs2 => ?_
      exact SepWP.done hpc2 hrun2
        ⟨rfl, hvm2, htr2, hsp2.trans hsp1.symm, hx0_2,
         hcs2.2.2.2.2.1.trans hx23_1, hcs2.2.2.2.2.2.2.2.1.trans hx26_1,
         hcs2.2.2.2.2.2.2.2.2.2.2.2⟩
    refine SepWP.bind_seq_readOnly hp1b (by sep_focus)
      fun s2 hpc2 hrun2 ⟨hcl2, hvm2, htr2, hsp2, hx0_2, hx23_2, hx26_2, hv2⟩ => ?_
    refine SepWP.bind_seq_readOnly
      (promote_b4_to_ec_placed_wp recPtr outPtr s2 hcl2 hpc2 hrun2 hx0_2 hx23_2 hx26_2)
      (emp_sepConj _).symm
      fun s3 hpc3 hrun3 ⟨hcl3, hvm3, htr3, hsp3, hx0_3, hx23_3, hv3⟩ => ?_
    have hvm_03 : VmPreserved s0 s3 := hvm1.trans (hvm2.trans hvm3)
    have htr_30 : s3.trace = s0.trace := htr3.trans (htr2.trans htr1)
    have hsp_30 : s3.sp = s0.sp - 1184#64 := hsp3.trans (hsp2.trans hsp1)
    have hv_30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
      have hv32 : calleeSavedVRegs s3 = calleeSavedVRegs s2 := by simp [calleeSavedVRegs, hv3]
      have hv10 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by simp [calleeSavedVRegs, hv1]
      exact hv32.trans (hv2.trans hv10)
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (cells_1248_8_eq_stack16 s0.sp).symm) (by sep_focus) ?_
    apply SepWP.mono
    · exact SepWP.frame_auto
        (promote_miss_from_ec_placed_wp s0 s3 recPtr prevPtr outPtr hcl3 hvm_03 hpc3 hrun3
          hsp_align' htr_30 hsp_30 hx0_3 hx23_3 hv_30)
    · intro sf _ _ _ ⟨hentf, hvmf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hvmf, Satisfies.mono (sepConj_mono_left ?_) hm⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 600000 in
/-- `HookSat` `black_box` sibling of `MatchCalleeBudget.promote_matching_session_key_miss_raw_placed_ok`. -/
theorem promote_matching_session_key_miss_raw_placed_ok_sat [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl promoteMatchingSessionKeyMissRawSpec) := by
  have hbb := black_box_placed_ok_sat h_bb
  clear h_bb
  refine subroutine_ok_of_sepWP_init
    fun ⟨recPtr, prevPtr, curDiscr, abkPtr, sessVer, msgVer, serPtr, outPtr, serBytes, ak⟩ R s0
      hpc hrun hpre hsp_align => ?_
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  dsimp only [promoteMatchingSessionKeyMissRawSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpec,
    sessionRecordMissPromoteFieldsAt] at hpre'
  dsimp only [withLsCodeLoaded, promoteMatchingSessionKeyMissRawSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpec,
    sessionRecordMissPromoteFieldsAt]
  refine ⟨_, hpre', ?_⟩
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
  obtain ⟨hx0, hx1, hx2, hx3, hx8, hcur, hver_eq, hklen, halen, hne⟩ := hpure
  have hcmn := cond_eq_adds64_one_false_over hcur
  have hveq_b : ((if (sessVer == 0#32) = true then 2#32 else sessVer) != msgVer.zeroExtend 32) = false := by
    simp only [beq_iff_eq, hver_eq, bne_self_eq_false]
  have hacc_false : ctBytesEqAcc serBytes ak true = false :=
    ctBytesEqAcc_true_of_ne (hklen.trans halen.symm) hne
  conv => arg 4; unfold promoteMissStackCells; rw [cells_1248_8_eq_stack16 s0.sp, cells_1184_split_2 s0.sp]
  have hp1 :
      SepWP ((blkPC_50).rebase (blkPl_50).base H) ((blkPl_50).base + 128#64) s0
        (((recPtr + 24#64) ↦₆₄ curDiscr) ∗
         ((recPtr + 128#64) ↦₆₄ abkPtr) ∗
         ((recPtr + 136#64) ↦₆₄ 33#64) ∗
         ((recPtr + 352#64) ↦₃₂ sessVer) ∗
         (∃∗ w4a0 : BitVec 64, (s0.sp - 1184#64) ↦₆₄ w4a0) ∗
         (∃∗ w470 : BitVec 64, (s0.sp - 1136#64) ↦₆₄ w470) ∗
         cells (s0.sp - 96#64) 12)
        (fun s1 P1 =>
          (P1 ⊢ ((recPtr + 24#64) ↦₆₄ curDiscr) ∗ ((recPtr + 128#64) ↦₆₄ abkPtr) ∗
            ((recPtr + 136#64) ↦₆₄ 33#64) ∗ ((recPtr + 352#64) ↦₃₂ sessVer) ∗
            ((s0.sp - 1184#64) ↦₆₄ 0#64) ∗ ((s0.sp - 1136#64) ↦₆₄ serPtr) ∗ promoteSavedRegs s0) ∧
          LibsignalCodeLoaded lsmpl s1.mem ∧
          VmPreserved s0 s1 ∧
          s1.trace = s0.trace ∧ s1.sp = s0.sp - 1184#64 ∧
          s1.readReg64 .x19 = abkPtr ∧ s1.readReg64 .x21 = 33#64 ∧
          s1.readReg64 .x22 = serPtr ∧ s1.readReg64 .x23 = outPtr ∧
          s1.readReg64 .x25 = 1#64 ∧ s1.readReg64 .x26 = recPtr ∧ s1.vregs = s0.vregs) := by
    apply sepWP_add_lscl_vm hcl0
    rw [cells_96_12_eq_over s0.sp]
    have hx0' : s0.readReg64 (Reg.gpr 0#5) = recPtr := hx0
    have hx1' : s0.readReg64 (Reg.gpr 1#5) = msgVer.zeroExtend 64 := hx1
    have hx2' : s0.readReg64 (Reg.gpr 2#5) = serPtr := hx2
    have hx3' : s0.readReg64 (Reg.gpr 3#5) = 33#64 := hx3
    have hx8' : s0.readReg64 (Reg.gpr 8#5) = outPtr := hx8
    wp_pull_exists
    by_vm_steps (
      wp_steps
      refine SepWP.done (by simp only [hpc, hcmn, hveq_b, hx3', wp_norm, arm64_norm])
        (by simp only [hrun, wp_norm, arm64_norm])
        ⟨by simp only [wp_norm, arm64_norm],
         ?_,
         by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
         by simp only [hx0', wp_norm, arm64_norm], by simp only [hx3', wp_norm, arm64_norm],
         by simp only [hx2', wp_norm, arm64_norm], by simp only [hx8', wp_norm, arm64_norm],
         by simp only [wp_norm, arm64_norm], by simp only [hx0', wp_norm, arm64_norm], rfl⟩
      unfold promoteSavedRegs
      sep_frame)
  apply SepWP.seq
  · exact SepWP.frame_auto hp1
  · intro s1 _ hpc1 hrun1 ⟨hent1, hcl1, hvm1, htr1, hsp1, hx19_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hv1⟩
    refine SepWP.weaken_pre hent1 ?_
    have hsp_align1 : (s1.sp &&& 15#64 == 0#64) = true := by
      rw [hsp1, sp_sub_1184_align_over]; exact hsp_align'
    have hloop := promote_ct_loop_gen_placed_wp hbb serBytes ak true (hklen.trans halen.symm)
      (by intro hn; rw [hn] at hklen; simp at hklen) (by rw [hklen]; decide)
      recPtr serPtr abkPtr outPtr s1 hpc1 hrun1 hsp_align1 hx19_1
      (by rw [hklen]; exact hx21_1) hx22_1 hx23_1 hx25_1 hx26_1
    rw [hacc_false] at hloop
    simp only [Bool.false_eq_true, ↓reduceIte] at hloop
    rw [hsp1] at hloop
    have hloop_cl := sepWP_add_lscl hcl1 hloop
    refine SepWP.bind_seq_readOnly hloop_cl (by sep_focus)
      fun s2 hpc2 hrun2 ⟨hcl2, hvm2, htr2, hsp2, hx0_2, hx23_2, hx26_2, hv2⟩ => ?_
    refine SepWP.bind_seq_readOnly
      (promote_b4_to_ec_placed_wp recPtr outPtr s2 hcl2 hpc2 hrun2 hx0_2 hx23_2 hx26_2)
      (emp_sepConj _).symm
      fun s3 hpc3 hrun3 ⟨hcl3, hvm3, htr3, hsp3, hx0_3, hx23_3, hv3⟩ => ?_
    have hvm_03 : VmPreserved s0 s3 := hvm1.trans (hvm2.trans hvm3)
    have htr_30 : s3.trace = s0.trace := htr3.trans (htr2.trans htr1)
    have hsp_30 : s3.sp = s0.sp - 1184#64 := hsp3.trans hsp2
    have hv_30 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
      have hv32 : calleeSavedVRegs s3 = calleeSavedVRegs s2 := by simp [calleeSavedVRegs, hv3]
      have hv10 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by simp [calleeSavedVRegs, hv1]
      exact hv32.trans (hv2.trans hv10)
    refine SepWP.focus_weaken (cells_1184_merge_2 s0.sp 0#64 serPtr) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (cells_1248_8_eq_stack16 s0.sp).symm) (by sep_focus) ?_
    apply SepWP.mono
    · exact SepWP.frame_auto
        (promote_miss_from_ec_placed_wp s0 s3 recPtr prevPtr outPtr hcl3 hvm_03 hpc3 hrun3
          hsp_align' htr_30 hsp_30 hx0_3 hx23_3 hv_30)
    · intro sf _ _ _ ⟨hentf, hvmf, htrf, hspf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hvmf, Satisfies.mono (sepConj_mono_left ?_) hm⟩
      refine Entails.trans hentf ?_
      rw [htrf]
      sep_frame
    · intro _ _ _ hf; exact hf

private theorem subroutine_ok_withLsCodeLoaded_vmPreserved_refine_frame {α β : Type}
    {prog : Program} {entry : BitVec 64} {pl : MultiPlacement}
    {inner : Spec α} {outer : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (withVmPreserved inner)))
    (href : ∀ (x : β) (R : SepProp) (s0 : State),
      (s0.mem ⊨ outer.pre x s0 ∗ R) →
      ∃ (y : α) (F : SepProp),
        (s0.mem ⊨ inner.pre y s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ inner.post y s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ outer.post x s0 sf ∗ R)))
    (hpanic : ∀ y R (s0 sf : State), ¬ (sf.mem ⊨ inner.onPanic y s0 sf ∗ R) := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (hexit : ∀ y code R (s0 sf : State), ¬ (sf.mem ⊨ inner.onExit y code s0 sf ∗ R) := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ x y F R (s0 sf : State),
      (sf.mem ⊨ inner.onOom y s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ outer.onOom x s0 sf ∗ R) := by
      intro _ _ _ _ _ _ ho; exact False.elim (not_satisfies_false_sepConj ho)) :
    subroutine_ok prog entry (withLsCodeLoaded pl (withVmPreserved outer)) := by
  refine subroutine_ok_refine_frame h (fun x R s0 hpre => ?_) hpanic hexit hoom
  have ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨y, F, hy_pre, hy_post⟩ := href x R s0 hpre'
  refine ⟨y, F, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, hy_pre⟩
  · dsimp only [withLsCodeLoaded, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hy_post sf hpost.2⟩

set_option maxHeartbeats 600000 in
/-- `HookSat` `black_box` sibling of `MatchCalleeBudget.promote_matching_session_record_over_placed_ok`. -/
theorem promote_matching_session_record_over_placed_ok_sat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionRecordOverSpec A)) := by
  refine subroutine_ok_by_cases
    (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
      BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
        x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32) ?_ ?_
  · refine subroutine_ok_by_cases
      (fun (x : BitVec 64 × BitVec 64 × BitVec 64 × SessionGhost × Session (List (BitVec 8)) ×
        BitVec 8 × BitVec 64 × BitVec 64 × List (BitVec 8)) =>
          x.2.2.2.2.1.aliceBaseKey.length = 33) ?_ ?_
    · -- Branch 3: 33-byte `aliceBaseKey ≠ key`
      have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
          (withLsCodeLoaded lsmpl (withVmPreserved
            { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A with
              pre := fun x s0 =>
                ⌜x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
                  (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A).pre x s0) })) := by
        refine subroutine_ok_withLsCodeLoaded_vmPreserved_refine_frame
          (promote_matching_session_key_miss_raw_placed_ok_sat h_bb) ?_
        intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
        dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hlen33, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hver, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, hmem⟩
        have hne_key : key ≠ sess.aliceBaseKey := fun hk => hmiss ⟨hver, hk.symm⟩
        have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
            ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
             (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
             stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        obtain ⟨hcap_ne, halice, hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
        have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
        have hal33 : G.alice.bytes.length = 33 := by rw [halice]; exact hlen33
        have hcapnz : G.alice.cap ≠ 0 := by
          intro h0
          have h1 : G.alice.cap.toNat = 0 := by simp [h0]
          rw [h1, hal33] at hle; omega
        have habk : BitVec.ofNat 64 G.alice.bytes.length = 33#64 := by rw [hal33]
        rw [habk, aliceBufOverAt_expose_33 A G sess.aliceBaseKey halice hlen33 hcapnz] at hexp
        refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr, sess.state.sessionVersion,
            msgVer, serPtr, outPtr, key, sess.aliceBaseKey⟩,
          sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗
            (A.live G.alice.ptr G.alice.cap.toNat 1 ∗
              memRegion (G.alice.ptr + 33#64) (G.alice.cap.toNat - 33)) ∗
            (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
        · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, hklen, hlen33, hne_key⟩, ?_⟩
          rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
        · intro sf hpost
          dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionKeyMissRawSpec,
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpost ⊢
          rw [hexp, stackAt_promoteMissStack_eq s0.sp]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      exact subroutine_ok_mono hsub
        (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
          dsimp only [withLsCodeLoaded, promoteMatchingSessionRecordOverSpec, withVmPreserved]
          sep_ac_rfl)) hp)
        (fun _ _ _ _ hq => hq)
    · -- Branch 2: `aliceBaseKey.length ≠ 33`
      have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
          (withLsCodeLoaded lsmpl (withVmPreserved
            { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A with
              pre := fun x s0 =>
                ⌜¬ x.2.2.2.2.1.aliceBaseKey.length = 33⌝ ∗
                  (⌜x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A).pre x s0) })) := by
        refine subroutine_ok_withLsCodeLoaded_vmPreserved_refine_frame
          (promote_matching_session_len_miss_raw_placed_ok_sat h_bb) ?_
        intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
        dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hlen_ne, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨hver, hpre⟩
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
        have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
            ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
             (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
             stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
          Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
        obtain ⟨hcap_ne, halice, hle, hlt⟩ := sessionRecordAt_miss_facts hrec_mem
        have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
        have habk_ne : BitVec.ofNat 64 G.alice.bytes.length ≠ 33#64 :=
          ofNat_len_ne_33 (Nat.lt_of_le_of_lt hle hlt) (by rw [halice]; exact hlen_ne)
        refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
            BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
            msgVer, serPtr, outPtr⟩,
          sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
            (serPtr ↦ₛ key) ∗
            (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
        · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpec]
          rw [sepConj_assoc, satisfies_pure_sepConj]
          refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver, habk_ne⟩, ?_⟩
          rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
        · intro sf hpost
          dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionLenMissRawSpec,
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpost ⊢
          rw [hexp, stackAt_promoteMissStack_eq s0.sp]
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      exact subroutine_ok_mono hsub
        (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
          dsimp only [withLsCodeLoaded, promoteMatchingSessionRecordOverSpec, withVmPreserved]
          sep_ac_rfl)) hp)
        (fun _ _ _ _ hq => hq)
  · -- Branch 1: Version mismatch (`sess.state.version ≠ msgVer.zeroExtend 32`)
    have hsub : subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
        (withLsCodeLoaded lsmpl (withVmPreserved
          { CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A with
            pre := fun x s0 =>
              ⌜¬ x.2.2.2.2.1.state.version = x.2.2.2.2.2.1.zeroExtend 32⌝ ∗
                (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec A).pre x s0 })) := by
      refine subroutine_ok_withLsCodeLoaded_vmPreserved_refine_frame
        promote_matching_session_ver_miss_raw_placed_ok ?_
      intro ⟨recPtr, prevCap, prevPtr, G, sess, msgVer, serPtr, outPtr, key⟩ R s0 hpre
      dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨hver_ne, hpre⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, _hmiss, _hklen⟩, hmem⟩
      have hrec_mem : s0.mem ⊨ sessionRecordAt A recPtr ⟨prevCap, prevPtr, some G⟩ ⟨some sess⟩ ∗
          ((serPtr ↦ₛ key) ∗ (∃∗ w0 : BitVec 64, outPtr ↦₆₄ w0) ∗
           (∃∗ b8 : BitVec 8, (outPtr + 8#64) ↦₈ b8) ∗
           stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
      obtain ⟨hcap_ne, _halice, _hle, _hlt⟩ := sessionRecordAt_miss_facts hrec_mem
      have hexp := sessionRecordAt_expose_miss A recPtr prevCap prevPtr G sess
      refine ⟨⟨recPtr, prevPtr, G.localIk.cap, G.alice.ptr,
          BitVec.ofNat 64 G.alice.bytes.length, sess.state.sessionVersion,
          msgVer, serPtr, outPtr⟩,
        sessionRecordMissRestAt A recPtr prevCap prevPtr G sess ∗ aliceBufOverAt A G ∗
          (serPtr ↦ₛ key) ∗
          (memRegion (s0.sp - 1104#64) 656 ∗ memRegion (s0.sp - 440#64) 344), ?_, ?_⟩
      · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpec]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hcap_ne, hver_ne⟩, ?_⟩
        rw [hexp, stackAt_promoteMissStack_eq s0.sp] at hrec_mem
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_mem
      · intro sf hpost
        dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionVerMissRawSpec,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec] at hpost ⊢
        rw [hexp, stackAt_promoteMissStack_eq s0.sp]
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    exact subroutine_ok_mono hsub
      (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
        dsimp only [withLsCodeLoaded, promoteMatchingSessionRecordOverSpec, withVmPreserved]
        sep_ac_rfl)) hp)
      (fun _ _ _ _ hq => hq)

set_option maxHeartbeats 400000 in
/-- `HookSat` `black_box` sibling of `MatchCalleeBudget.promote_matching_session_miss_placed_ok`. -/
theorem promote_matching_session_miss_placed_ok_sat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_50).rebase (blkPl_50).base H) (blkPl_50).base
      (withLsCodeLoaded lsmpl (promoteMatchingSessionMissSpec A)) := by
  refine subroutine_ok_withLsCodeLoaded_vmPreserved_refine_frame
    (promote_matching_session_record_over_placed_ok_sat (A := A) h_bb) ?_
  intro x R s0 hpre
  dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx8, hcur, hmiss, hklen⟩, hmem⟩
  have hrec_sat : s0.mem ⊨ sessionRecordAt A x.recPtr x.g x.r ∗
      ((x.serPtr ↦ₛ x.serBytes) ∗ memRegion x.outPtr 16 ∗
       stackAt s0.sp promoteMatchingSessionMissStack ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hg_some : ∃ G : SessionGhost, x.g.cur = some G := by
    have hrec_l := Satisfies.of_sep_left hrec_sat
    unfold sessionRecordAt at hrec_l
    rw [hcur] at hrec_l
    cases hgc : x.g.cur with
    | none =>
      rw [hgc] at hrec_l
      have hf := Satisfies.of_sep_right hrec_l
      rw [satisfies_pure] at hf
      exact False.elim hf
    | some G => exact ⟨G, rfl⟩
  obtain ⟨G, hgc⟩ := hg_some
  have hrec_eq : sessionRecordAt A x.recPtr x.g x.r =
      sessionRecordAt A x.recPtr ⟨x.g.prevCap, x.g.prevPtr, some G⟩ ⟨some x.s⟩ := by
    unfold sessionRecordAt
    rw [hgc, hcur]
  refine ⟨(x.recPtr, x.g.prevCap, x.g.prevPtr, G, x.s, x.msgVer, x.serPtr, x.outPtr, x.serBytes),
    memRegion (x.outPtr + 9#64) 7, ?_, ?_⟩
  · dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hx8, hmiss, hklen⟩, ?_⟩
    rw [hrec_eq, outRegion16_split_over x.outPtr] at hrec_sat
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrec_sat
  · intro sf hpost
    dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionRecordOverSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.promoteMatchingSessionMissSpec] at hpost ⊢
    rw [hrec_eq]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

end LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCalleeBudgetSat
