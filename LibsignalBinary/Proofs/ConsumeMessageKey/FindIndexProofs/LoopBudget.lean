/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import ProofLib.SepLogic.WP.Apply

/-!
# `VmPreserved` Relocatable Contracts for `find_receiver_chain_index` (Blocks 26, 201, 212, 213)
-/

@[expose] public section

namespace LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Arm64 ProofLib
open CryptoGames.LibsignalSession (PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement
  blkLib_eq_26 blkLib_eq_201 blkLib_eq_212
  blkPC_26 blkPC_201 blkPC_212 blkPC_213
  blkPl_26 blkPl_201 blkPl_212 blkPl_213
  lsBlackBoxU8Sym lsLogFilterAddr ls_externAt?_of_mem
  ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain ls_subroutine_ok_of_block
  lsmpl lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain
  withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalSession (FindIndexGhost blackBoxHook)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (
  DeserGhost SepWP_chainAt_info SepWP_entails_pre SepWP_sepExists
  add_120_eq_add_104_add_16 after_heq_placed_entails
  and32_1_ite_1_0 and32_ite_1_0 and64_1_ite_1_0 and64_ite_1_0
  and64_mask255_ite_1_0 and64_mask32_ite_1_0 arrayAt_cons_sep_pre
  byte_bne_zext32 cells_208_unfold cells_96_unfold chainAt_eq_of_ok
  csinc_eq_zero32_ite_1_0 ctEqSliceSpec ct_eq_bool_32
  deserializePlacedSpec entails_stackAt_1024 eqStack
  findIdx?_map_cons_neg findIdx?_map_cons_pos findIdxStack_split
  idx_len_step_of_cons_cons idx_lt_two_pow_64_of_cons ite_bne_byte_0_1
  len_mul_104_step_of_cons_cons length_lt_cons
  list_cons_cons_mul_104_ne_104 list_cons_mul_104_sub_104 list_length_induction
  loopStack loopStack_entails_stackAt
  memRegion_16_eq_stackFrameFor_eq memRegion_33_eq memRegion_48_eq_stackFrameFor_ct_eq
  ofNat_idx_add_one pk_208_eq_sep pk_247_eq_sep
  pointsToBytes32 pointsToBytes_deserialize_split pointsToBytes_eq_pointsToBytes32
  publicKeyEqSpec publicKey_bytes_toList_length
  publicKey_deserialize_ok_inversion publicKey_ite_toList_eq
  reg_mul_104_eq_ofNat
  setWidth32_ite_1_0 setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 setWidth8_ite_1_0
  sp_sub_248_orr_1 stackFrameFor_ctEq_eq_cells_ext32
  toNat_ofNat_of_lt zero_add_len_lt_of_mul_104
)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)

/-! ## `VmPreserved` Lifting Across `subtle::black_box::<u8>` (Block 213) -/

/-- Hook table mapping `lsBlackBoxU8Sym` to `blackBoxHook` and trapping all other externs. -/
def bbTrapHooks : String → Option (State → State) :=
  fun n => if n = lsBlackBoxU8Sym then some blackBoxHook else trapHooks n

private theorem findSome?_override_none :
    ∀ (l : List (String × Nat)) (off : Nat),
      (l.findSome? fun (_n, o) => if o == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | (_n, _o) :: tl, off => by
    dsimp only [List.findSome?]
    rw [ite_self]
    exact findSome?_override_none tl off

private theorem findSome?_bbTrapHooks_some {Hk : String → Option (State → State)}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then bbTrapHooks n else none) = some f →
      (f = fun s => s.setStatus (.Exception "extern")) ∨
        (f = blackBoxHook ∧
          (l.findSome? fun (n, o) => if o == off then Hk n else none) = some blackBoxHook)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : n = lsBlackBoxU8Sym
      · subst hn
        simp only [bbTrapHooks, ↓reduceIte, Option.some.injEq] at h
        rw [h_bb]
        exact Or.inr ⟨h.symm, rfl⟩
      · simp only [bbTrapHooks, hn, ↓reduceIte, trapHooks, Option.some.injEq] at h
        exact Or.inl h.symm
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_bbTrapHooks_some h_bb tl h

private theorem findSome?_stubs_eq_none_of_bbTrapHooks (Hk : String → Option (State → State)) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then bbTrapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    simp only [List.findSome?_cons] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte, bbTrapHooks, trapHooks] at h
      by_cases hn : n = lsBlackBoxU8Sym <;> simp [hn] at h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_eq_none_of_bbTrapHooks Hk tl h

private theorem externAt?_rebase_bbTrapHooks_some {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)} {f : State → State}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    (h : ((P.rebase b bbTrapHooks).withSvc noSyscalls).externAt? pc = some f) :
    (f = fun s => s.setStatus (.Exception "extern")) ∨
      (f = blackBoxHook ∧ (P.rebase b Hk).externAt? pc = some blackBoxHook) := by
  unfold Program.withSvc at h
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢
  dsimp only at h ⊢
  rw [findSome?_override_none] at h ⊢
  cases hm : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then bbTrapHooks n else none) with
  | none =>
    rw [hm] at h
    cases h
  | some g =>
    rw [hm] at h
    injection h with hgf
    subst hgf
    rcases findSome?_bbTrapHooks_some h_bb P.stubs hm with htrap | ⟨hbb, hhk⟩
    · exact Or.inl htrap
    · rw [hhk]
      exact Or.inr ⟨hbb, rfl⟩

private theorem externAt?_rebase_eq_none_of_bbTrapHooks {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)}
    (h : (P.rebase b bbTrapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢
  dsimp only at h ⊢
  rw [findSome?_override_none] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then bbTrapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then bbTrapHooks n else none) with
    | none => rfl
    | some g =>
      rw [hm] at h
      cases h
  rw [findSome?_stubs_eq_none_of_bbTrapHooks Hk P.stubs h1]
  rfl

private theorem steps_rebase_bbTrapHooks_noSyscalls {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    {s sm : State}
    (hsteps : Steps ((P.rebase b bbTrapHooks).withSvc noSyscalls) s sm)
    (hrun_m : sm.status = .Running) :
    Steps (P.rebase b Hk) s sm ∧ ProofLib.StdStartup.VmFieldsPreserved s sm ∧ sm.fs = s.fs := by
  induction hsteps with
  | refl => exact ⟨Steps.refl _, ProofLib.StdStartup.VmFieldsPreserved.refl _, rfl⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_m
      | step hs _ => cases hs <;> assumption
    rcases ih hrun_m with ⟨hsteps_rest, hvm_rest, hfs_rest⟩
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern_fault _ _ _ => cases s1; cases hr2
    | extern hr1 hext hkeep hsym =>
      rcases externAt?_rebase_bbTrapHooks_some h_bb hext with rfl | ⟨rfl, hext_hk⟩
      · cases s1; cases hr2
      · have hvm_bb : ProofLib.StdStartup.VmFieldsPreserved s1 (blackBoxHook s1) :=
          ⟨rfl, rfl, rfl, fun _ => rfl⟩
        exact ⟨Steps.step (Step.extern hr1 hext_hk hkeep hsym) hsteps_rest,
          ProofLib.StdStartup.VmFieldsPreserved.trans hvm_bb hvm_rest,
          hfs_rest.trans (by cases s1; rfl)⟩
    | @exec inst hr1 hfe =>
      have hext_trap : (P.rebase b bbTrapHooks).externAt? s1.pc = none := by
        cases he : (P.rebase b bbTrapHooks).externAt? s1.pc with
        | none => rfl
        | some g =>
          unfold Program.fetchMem Program.withSvc at hfe
          change (if (Program.externAt? (P.rebase b bbTrapHooks) s1.pc).isSome then none else _) =
              some inst at hfe
          rw [he] at hfe
          cases hfe
      have hfeH : (P.rebase b Hk).fetchMem s1.mem s1.pc = some inst := by
        have hext_hk := externAt?_rebase_eq_none_of_bbTrapHooks (Hk := Hk) hext_trap
        unfold Program.fetchMem at hfe ⊢
        change (if (Program.externAt? (P.rebase b bbTrapHooks) s1.pc).isSome then none else _) =
            some inst at hfe
        rw [hext_trap] at hfe
        rw [hext_hk]
        exact hfe
      have hnsvc0 : inst.isSvc0 = false := by
        cases ht : inst.isSvc0 with
        | false => rfl
        | true =>
          cases inst with
          | system isHalt imm =>
            cases isHalt with
            | true => simp [Instr.isSvc0] at ht
            | false =>
              simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at ht
              subst ht
              cases s1; cases hr2
          | _ => simp [Instr.isSvc0] at ht
      have hev1 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        ((P.rebase b bbTrapHooks).withSvc noSyscalls) hnsvc0 s1
      have hev2 := ProofLib.StdStartup.evalInst_eq_execInst_of_not_isSvc0
        (P.rebase b Hk) hnsvc0 s1
      rw [hev1] at hsteps_rest hvm_rest hfs_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest,
        hfs_rest.trans (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2⟩

theorem sepWP_rebase_bb_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b bbTrapHooks).withSvc noSyscalls) target_pc s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ post sm Pm)) :
    SepWP (P.rebase b Hk) target_pc s Pre (fun sm Pm => VmPreserved s sm ∧ post sm Pm) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : ((P.rebase b bbTrapHooks).withSvc noSyscalls).CodeLoaded s.mem :=
    hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL'
  rcases hout with ⟨hpc, hrun, Pm, hPm, htp, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_hk, hvm, hfs⟩ := steps_rebase_bbTrapHooks_noSyscalls h_bb hsteps hrun
    exact ⟨sm, hsteps_hk, Or.inl ⟨hpc, hrun, Pm, hPm,
      VmPreserved.of_vm_tpidr hvm htp (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs), hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem externAt?_bbTrapHooks_213 [LibsignalPlacement] :
    ((blkPC_213).rebase (blkPl_213).base bbTrapHooks).externAt?
      (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
  (ls_externAt?_of_mem (H := bbTrapHooks)).trans (by simp [bbTrapHooks])

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

syntax "by_bb_vm_steps " ident tacticSeq : tactic

elab_rules : tactic
  | `(tactic| by_bb_vm_steps $h_bb:ident $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.sepWP_rebase_bb_vmPreserved $h_bb))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
        throwError "by_bb_vm_steps: expected `SepWP`, got{Lean.indentExpr ty}"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_bb_vm_steps: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_bb_vm_steps: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
        else if sub.isAppOfArity ``Arm64.Program.rebase 4 &&
            (sub.getArg! 2).cleanupAnnotations.isConstOf
              ``LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget.bbTrapHooks then
          some e2
        else if sub.eqv e1 then some e2
        else none
      g.assign prf2

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp]
  byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0
  and64_mask32_ite_1_0 and32_ite_1_0 and32_1_ite_1_0
  publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0
attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

/-! ## `VmPreserved` Contracts for Blocks 201, 212, and 213 -/

def deserializePlacedBudgetSpec [LibsignalPlacement] : Spec DeserGhost :=
  withVmPreserved deserializePlacedSpec

def deserializeMemPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) :=
  withVmPreserved CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeMemPlacedSpec

noncomputable def ctEqSliceBudgetSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceSpec

noncomputable def publicKeyEqBudgetSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqSpec

def publicKeyEqMemSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec

set_option maxHeartbeats 1600000 in
theorem ct_eq_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceBudgetSpec := by
  have hext : ((blkPC_213).rebase (blkPl_213).base bbTrapHooks).externAt?
      (lsρ lsBlackBoxU8Sym) = some blackBoxHook := externAt?_bbTrapHooks_213
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  clear hpre
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  unfold State.spAligned at hsp_align
  dsimp only [ctEqSliceSpec, Reg.x0, Reg.x1, Reg.x30, Reg.lr] at *
  simp only [sepConj_assoc]
  by_bb_vm_steps h_bb (
    refine SepWP.pure_elim ?_
    rintro ⟨hx0, hx1, hsp, hk1, hk2⟩
    subst hx0 hx1 hsp
    rw [stackFrameFor_ctEq_eq_cells_ext32 s0.sp]
    cells_unfold
    wp_pull_exists
    rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) hk1,
      pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 1#5)) hk2]
    unfold pointsToBytes32
    simp only [sepConj_assoc]
    iterate 33 (wp_steps; wp_black_box hext)
    rw [ct_eq_bool_32 hk1 hk2]
    wp_done)

section VmProofs
attribute [local irreducible] VmPreserved

theorem deserialize_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H)
      (blkPl_201).base deserializePlacedBudgetSpec := by
  simp only [deserializePlacedBudgetSpec, withVmPreserved, deserializePlacedSpec, sepConj_assoc]
  wp_init g s0
  rcases g with ⟨ptr, bs, pk, sret, tag0, out32⟩
  dsimp only at *
  have hx0 : s0.readReg64 .x0 = ptr := by assumption
  have hx1 : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx8 : s0.readReg64 .x8 = sret := by assumption
  have hdeser_ok : PublicKey.deserialize bs = .ok pk := by assumption
  have hout_len : out32.length = 32 := by assumption
  subst hx0 hx8
  obtain ⟨_, hge33⟩ := publicKey_deserialize_ok_inversion hdeser_ok
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := pk.bytes.toList) (by simp)
  obtain ⟨u0, u1, u2, u3, _, hout_cells⟩ :=
    exists_unpack64_of_length_32 (bs := out32) hout_len
  rw [pointsToBytes_deserialize_split (s0.readReg64 (Reg.gpr 0#5)) hdeser_ok,
    hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
    hout_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply sepWP_seg_ls_vm
    (Q := (blkPC_201).rebase (blkPl_201).base (hooksException H))
    blkLib_eq_201 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip
  wp_steps
  wp_if hcs
  · simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      hx1, decide_eq_true_eq] at hcs
    omega
  · wp_step
    wp_if hcbz9
    · wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm ⊢
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      try simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, hvm]
      wp_done
    · wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      have hvm : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm ⊢
      rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
      try simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, hvm]
      wp_done

theorem deserializeMem_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (blkPl_201).base
      deserializeMemPlacedSpec := by
  refine subroutine_ok_map (deserialize_vm_placed_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeMemPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeMemPlacedSpec,
    memRegion_33_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    satisfies_sepExists] at hpre
  rcases hpre with ⟨tag0, out32, hpre⟩
  rw [satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlt, hdeser⟩, hpre⟩
  rw [sepConj_pure_left_comm (ptr ↦ₛ bs), satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hout32, hpre⟩
  refine ⟨(ptr, bs, pk, sret, tag0, out32), R, ?_, ?_⟩
  · dsimp only [deserializePlacedBudgetSpec, withVmPreserved, deserializePlacedSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlt, hdeser, hout32⟩, hpre⟩
  · intro sf hpost
    simpa only [deserializePlacedBudgetSpec, deserializeMemPlacedSpec, withVmPreserved,
      deserializePlacedSpec,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeMemPlacedSpec,
      sepConj_assoc] using hpost

theorem publicKey_eq_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqBudgetSpec) := by
  simp only [withLsCodeLoaded, publicKeyEqBudgetSpec, withVmPreserved, publicKeyEqSpec,
    sepConj_assoc]
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      ctEqSliceBudgetSpec := ct_eq_placed_ok h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, ctEqSliceBudgetSpec, withVmPreserved, ctEqSliceSpec,
    sepConj_assoc] at hct
  wp_init x s0
  obtain ⟨p1, pk1, p2, pk2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  apply sepWP_seq_lscl h (mid := lsmpl.base 213)
  apply sepWP_seg_ls_vm (Q := (blkPC_212).rebase (blkPl_212).base (hooksException H))
    blkLib_eq_212 (mid := lsmpl.base 213); intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  apply sepWP_seg_ls_vm (Q := (blkPC_212).rebase (blkPl_212).base (hooksException H))
    blkLib_eq_212 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
  try simp only [sepConj_assoc, hvm_tot]
  wp_done

theorem publicKeyEqMem_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) := by
  refine subroutine_ok_map (publicKey_eq_placed_ok h_bb) ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqBudgetSpec, publicKeyEqMemSpec,
      withVmPreserved, publicKeyEqSpec,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqBudgetSpec, publicKeyEqMemSpec,
      withVmPreserved, publicKeyEqSpec,
      CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpost

private theorem vmPreserved_setPC_left {s : State} {pc : BitVec 64} :
    VmPreserved s (s.setPC pc) := by
  simp [VmPreserved, LibsignalBinary.Heap.PoolPreserved, LibsignalBinary.Heap.FdsHiFrame,
    State.setPC]

private theorem vmPreserved_setPC_setMem {s : State} {pc1 pc2 : BitVec 64} {m : Memory} :
    VmPreserved ((s.setPC pc1).setMem m) ((s.setPC pc2).setMem m) := by
  simp [VmPreserved, LibsignalBinary.Heap.PoolPreserved, LibsignalBinary.Heap.FdsHiFrame,
    State.setPC, State.setMem]

/-! ## `VmPreserved` Contract for Block 26 (`find_receiver_chain_index`) -/

set_option maxHeartbeats 1600000 in
theorem find_loop_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64) (idx : Nat) (P_pre : SepProp)
    (u0 u1 u2 u3 : BitVec 64) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = BitVec.ofNat 64 idx)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 ∧ VmPreserved s0 s)
    (hidx_len : idx + (gc :: rest).length < 2 ^ 63)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜VmPreserved s0 sf ∧
              (sf.trace = s0.trace ∧
                match Option.map (· + idx)
                  ((List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their)) with
                | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
                | none => sf.readReg64 .x0 = 0#64)⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗ P_pre ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hdeser0 : subroutine_ok ((blkPC_201).rebase (blkPl_201).base H) (lsmpl.base 201)
      deserializeMemPlacedSpec :=
    deserializeMem_placed_ok H
  have hdeser := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) hdeser0
  simp only [withLsCl, deserializeMemPlacedSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeMemPlacedSpec,
    sepConj_assoc] at hdeser
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemSpec) :=
    publicKeyEqMem_placed_ok h_bb
  have heq := ls_subroutine_ok_cl_of_block
    (callerProg := (blkPC_26).rebase (blkPl_26).base H) heq0
  simp only [withLsCl, publicKeyEqMemSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec,
    sepConj_assoc] at heq
  induction rest using list_length_induction generalizing gc cur_p idx P_pre u0 u1 u2 u3 s with
  | h rest ih =>
    conv =>
      arg 4
      dsimp only [arrayAt]
      simp only [sepConj_assoc]
    apply SepWP_chainAt_info
    intro h1 h2 hcap hlen
    conv =>
      arg 4
      rw [chainAt_eq_of_ok A gc cur_p h1 h2 hcap]
      simp only [sepConj_assoc]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 201)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := lsmpl.base 201); intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm_s1 : VmPreserved s _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_s1 ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl1 => ?_
    wp_apply
    have hvm_after_deser : VmPreserved s0 _ :=
      htrace.2.2.trans (hvm_s1.trans (by assumption : VmPreserved _ _))
    simp only [hsp, hx19, hx20, hx21, hx22, hx23, hx24, htrace.1, htrace.2.1] at *
    obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
      exists_unpack64_of_length_32 (bs := gc.2.senderRatchetKey.bytes.toList) (by simp)
    rw [← pk_247_eq_sep _ hpk_cells]
    apply sepWP_seq_lscl (by assumption) (mid := lsmpl.base 212)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := lsmpl.base 212); intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm_s2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_s2 ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl2 => ?_
    rw [pk_247_eq_sep _ hpk_cells, pk_208_eq_sep _ hpk_cells]
    wp_apply
    have hvm_after_eq : VmPreserved s0 _ :=
      hvm_after_deser.trans (hvm_s2.trans (by assumption : VmPreserved _ _))
    simp only [hsp_sf, h, h_1, h_2, h_3, h_4, h_5, hvregs, hpost] at *
    refine SepWP_entails_pre
      (after_heq_placed_entails A s0 theirA their gc rest cur_p P_pre w0 w1 w2 w3 h1 h2 hcap hpk_cells) ?_
    wp_steps
    wp_if hmatch
    · dsimp only [loopStack]
      apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
        blkLib_eq_26 (mid := s0.readReg64 .lr); intro _m_strip3
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
      have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
      simp only [State.setMem_setMem] at hvm_s3 ⊢
      have hvm_fin : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
      rw [findIdx?_map_cons_pos idx (beq_iff_eq.mpr hmatch)]
      have hidx_toNat : (BitVec.ofNat 64 idx).toNat = idx :=
        toNat_ofNat_of_lt (idx_lt_two_pow_64_of_cons hidx_len)
      refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
      simp only [hvm_fin, true_and]
      wp_done
    · have hmatch_b : ¬(gc.2.senderRatchetKey == their) = true := by
        rw [beq_iff_eq]; exact hmatch
      rw [findIdx?_map_cons_neg idx hmatch_b]
      rcases rest with _ | ⟨gc', rest'⟩
      · simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul] at *
        dsimp only [loopStack]
        apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
          blkLib_eq_26 (mid := s0.readReg64 .lr); intro _m_strip3
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        simp only [State.setMem_setMem] at hvm_s3 ⊢
        have hvm_fin : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
        simp only [List.map_nil, List.findIdx?_nil, Option.map_none]
        refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (loopStack_entails_stackAt s0 w0 w1 w2 w3))))) ?_
        try simp only [hvm_fin, true_and]
        wp_done
      · apply sepWP_seq_lscl (by assumption) (mid := (blkPl_26).base + 136#64)
        apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
          blkLib_eq_26 (mid := (blkPl_26).base + 136#64); intro _m_strip3
        wp_steps
        rw [list_cons_cons_mul_104_ne_104 gc gc' rest' hlen_lt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real3 _hnsp3 => ?_
        have hvm_s3 : VmPreserved _ _ := _hnsp3.toVmPreserved (by wp_norm_lhs)
        simp only [State.setMem_setMem] at hvm_s3 ⊢
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_next => ?_
        have hvm_next : VmPreserved s0 _ := hvm_after_eq.trans (vmPreserved_setPC_left.trans hvm_s3)
        rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        conv =>
          arg 5; ext sf P_f
          rw [arrayAt_cons_sep_pre (chainAt A) gc (gc' :: rest') cur_p P_pre]
        refine ih rest' (length_lt_cons gc' rest') gc' (cur_p + 104#64) (idx + 1)
          (chainAt A gc cur_p ∗ P_pre) w0 w1 w2 w3 _ hcl_next ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · wp_norm_lhs
        · wp_norm_lhs
        · simp only [wp_norm, arm64_norm, *]
        · exact ofNat_idx_add_one idx
        · simp only [wp_norm, arm64_norm, *]
        · simp only [wp_norm, arm64_norm, *]
        · exact list_cons_mul_104_sub_104 gc (gc' :: rest')
        · simp only [wp_norm, arm64_norm, *]
        · exact add_120_eq_add_104_add_16 cur_p
        · exact ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *], hvm_next⟩
        · exact idx_len_step_of_cons_cons hidx_len
        · exact len_mul_104_step_of_cons_cons hlen_lt

set_option maxHeartbeats 800000 in
theorem find_loop_placed_ok_zero [LibsignalPlacement] {H : String → Option (State → State)}
    (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (s0 : State) (theirA : BitVec 64) (their : PublicKey) (R : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (rest : List (ChainGhost × ReceiverChain))
    (gc : ChainGhost × ReceiverChain)
    (cur_p : BitVec 64)
    {u0 u1 u2 u3 : BitVec 64} {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_26).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 0#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = theirA)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 1#64)
    (hx22 : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 ((gc :: rest).length * 104))
    (hx23 : s.readReg64 (Reg.gpr 23#5) = s0.sp - 247#64)
    (hx24 : s.readReg64 (Reg.gpr 24#5) = cur_p + 16#64)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0 ∧ VmPreserved s0 s)
    (hlen_lt : (gc :: rest).length * 104 < 2 ^ 63) :
    SepWP ((blkPC_26).rebase (blkPl_26).base H) (s0.readReg64 .lr) s
      (arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
        (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        loopStack s0 u0 u1 u2 u3)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            ⌜VmPreserved s0 sf ∧
              (sf.trace = s0.trace ∧
                match (List.map (·.2) (gc :: rest)).findIdx? (fun c => c.senderRatchetKey == their) with
                | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
                | none => sf.readReg64 .x0 = 0#64)⌝ ∗
            arrayAt (chainAt A) 104 cur_p (gc :: rest) ∗
            (theirA ↦ₛ their.bytes.toList) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            stackAt s0.sp 1024 ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have h := find_loop_placed_ok A h_bb s0 theirA their R hsp0 rest gc cur_p 0 emp u0 u1 u2 u3 s
    hcl hpc hrun hsp hx19 hx20 hx21 hx22 hx23 hx24 htrace
    (zero_add_len_lt_of_mul_104 hlen_lt) hlen_lt
  simpa only [emp_sepConj, Nat.add_zero, Option.map_id'] using h

def findPlacedAllocSpec [LibsignalPlacement] (A : RustAlloc) : Spec FindIndexGhost :=
  withVmPreserved (CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec A)

def findPlacedSpec [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M) :
    Spec FindIndexGhost :=
  findPlacedAllocSpec A.repAlloc

theorem find_receiver_chain_index_alloc_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)} (A : RustAlloc)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedAllocSpec A)) := by
  simp only [withLsCodeLoaded, findPlacedAllocSpec, withVmPreserved,
    CryptoVerification.LibsignalSession.FindReceiverChainIndex.findPlacedSpec, sepConj_assoc]
  wp_init g s0
  obtain ⟨p, cs, theirA, their⟩ := g
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst h_2 h_4
  conv =>
    arg 4
    rw [findIdxStack_split s0.sp, cells_208_unfold s0.sp, cells_96_unfold s0.sp]
    simp only [eqStack, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  iterate 16 (apply SepWP_sepExists; intro _)
  apply sepWP_seq_lscl hcl0 (mid := (blkPl_26).base + 32#64)
  apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
    blkLib_eq_26 (mid := (blkPl_26).base + 32#64); intro _m_strip0
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  have hvm0 : VmPreserved s0 _ := _hnsp0.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm0 ⊢
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_pro => ?_
  wp_steps
  wp_if hcbz
  · apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip_nil
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_nil _hnsp_nil => ?_
    have hvm_nil : VmPreserved s0 _ :=
      hvm0.trans (vmPreserved_setPC_setMem.trans (_hnsp_nil.toVmPreserved (by wp_norm_lhs)))
    simp only [State.setMem_setMem] at hvm_nil ⊢
    have hcs_nil : cs = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← h_3, hcbz]
      rfl
    subst hcs_nil
    simp only [List.map_nil, List.findIdx?_nil]
    refine SepWP_entails_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_stackAt_1024 s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)))) ?_
    try simp only [sepConj_assoc, hvm_nil]
    wp_done
  · apply sepWP_seq_lscl (by simpa [State.setPC] using hcl_pro) (mid := (blkPl_26).base + 136#64)
    apply sepWP_seg_ls_vm (Q := (blkPC_26).rebase (blkPl_26).base (hooksException H))
      blkLib_eq_26 (mid := (blkPl_26).base + 136#64); intro _m_strip_go
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real_go _hnsp_go => ?_
    have hvm_go : VmPreserved s0 _ :=
      hvm0.trans (vmPreserved_setPC_setMem.trans (_hnsp_go.toVmPreserved (by wp_norm_lhs)))
    simp only [State.setMem_setMem] at hvm_go ⊢
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_go => ?_
    rcases cs with _ | ⟨gc, rest⟩
    · exfalso
      apply hcbz
      apply BitVec.eq_of_toNat_eq
      simpa using h_3
    · simp only [sepConj_assoc]
      refine SepWP.mono (find_loop_placed_ok_zero A h_bb s0 (s0.readReg64 (Reg.gpr 2#5)) their R h_1
        rest gc (s0.readReg64 (Reg.gpr 0#5)) hcl_go (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by simpa only [wp_norm, arm64_norm] using reg_mul_104_eq_ofNat h_3)
        (by simpa only [wp_norm, arm64_norm] using sp_sub_248_orr_1 h_1)
        (by wp_norm_lhs)
        ⟨by wp_norm_lhs, by wp_norm_lhs, hvm_go⟩ h_5)
        fun sf P_f _ _ ⟨hmf, hsp_f, hcs_f⟩ => ⟨fun hm => ?_, hsp_f, hcs_f⟩
      have hm' := hmf hm
      rw [satisfies_pure_sepConj] at hm' ⊢
      rw [satisfies_pure_sepConj]
      exact ⟨hm'.1.1, hm'.1.2, hm'.2⟩

theorem find_receiver_chain_index_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {H : String → Option (State → State)} (A : RustCliAllocBudget M)
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_26).rebase (blkPl_26).base H) (blkPl_26).base
      (withLsCodeLoaded lsmpl (findPlacedSpec A)) :=
  find_receiver_chain_index_alloc_placed_ok A.repAlloc h_bb

end VmProofs

end LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
