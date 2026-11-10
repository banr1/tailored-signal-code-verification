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
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSteps
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import ProofLib.RegChain
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget & `VmPreserved` Relocatable Step Lemmas for `IdentityKeysSteps`

Provides budget-threaded `clearUpkSpecWithStack`, `VmPreserved`-strengthened subroutine contracts
for blocks `213` (`black_box::<u8>`), `212` (`PublicKey::eq`), `17` (`IdentityKey::is_same_account`),
`211` (`PublicKey::try_from`), and `28` (`SessionState::local_identity_key`), and `VmPreserved`
reachability steps on block `130`.
-/

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkLib_eq_211 blkLib_eq_212
  blkPC_211 blkPC_212 blkPC_213 blkPl_211 blkPl_212 blkPl_213
  lsBlackBoxU8Sym ls_externAt?_of_mem ls_subroutine_ok_of_block lsmpl lsρ
  sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (sessionStateAt)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex (
  and32_1_ite_1_0 and32_ite_1_0 and64_1_ite_1_0 and64_ite_1_0
  and64_mask255_ite_1_0 and64_mask32_ite_1_0 byte_bne_zext32
  csinc_eq_zero32_ite_1_0 ctEqSliceSpec ct_eq_bool_32
  deserializeMemPlacedSpec deserializePlacedSpec ite_bne_byte_0_1
  memRegion_16_eq_stackFrameFor_eq memRegion_33_eq memRegion_48_eq_stackFrameFor_ct_eq
  pointsToBytes32 pointsToBytes_deserialize_split pointsToBytes_eq_pointsToBytes32
  publicKeyEqMemSpec publicKeyEqSpec publicKey_bytes_toList_length
  publicKey_deserialize_ok_inversion publicKey_ite_toList_eq
  setWidth32_ite_1_0 setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 setWidth8_ite_1_0
  stackFrameFor_ctEq_eq_cells_ext32
)
open CryptoVerification.LibsignalTripleRatchet (TryDecryptGhost logOff rootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  ClearUpkGhost IsSameAccountGhost blkLib_eq_17 blkPC_17 blkPl_17
  isSameAccountSpec isSameAccountStack localIdentityKeyStack localIdentityOkAt
  remoteIdentityKeyStack remoteIdentityOkAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  blkPC_131 blkPl_131 exists_localGroupA_of_length_32 exists_word64_of_memRegion_8
  identityKeys_prologue_extract identityKeys_step2_extract identityKeys_step2_recombine
  identityKeys_step4_extract localGroupA localGroupA_eq_localGroupB remoteGroupC
  sepWP_to_reaches_pc stackAt_tryDecryptSubStack_sub tryDecryptDummyImg words4At words8At
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FdsHiFrame FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  localIdentityKeyPlacedSpec remoteIdentityKeyPlacedSpec
)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Case2Budget (
  deserializePlacedBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget (
  identityKeys_call_remote_ik_wp_placed identityKeys_copy_local_ik_wp_placed
  identityKeys_prologue_wp_placed identityKeys_remote_ik_common_wp_placed
  identityKeys_remote_none_wp_placed
)

@[expose] public section

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0
  and64_mask32_ite_1_0 and32_ite_1_0 and32_1_ite_1_0
  publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0
attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

/-! ## 1. Budget `clearUpkSpecWithStack` (`FreeOnlyEvs`, `0` `FitsEnv`) -/

def clearUpkSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (ClearUpkGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗
      stackAt s.sp (32 + hookStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionStateAt A.repAlloc x.ss { x.G with pending := none, kyber := none }
        x.st.clearUnacknowledgedPreKeyMessage ∗
      (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (32 + hookStack)

/-! ## 2. `VmPreserved` Lifting Across `subtle::black_box::<u8>` (Block `213`) -/

/-- Hook table executing `blackBoxHook` at `lsBlackBoxU8Sym` and trapping on all other externs. -/
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
          hfs_rest⟩
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
      have hfs_step : (execInst inst s1).fs = s1.fs :=
        (ProofLib.execInst_brk_oracle_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2
      rw [hev1] at hsteps_rest hvm_rest hfs_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest,
        hfs_rest.trans hfs_step⟩

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
    exact ⟨sm, hsteps_hk,
      Or.inl ⟨hpc, hrun, Pm, hPm, VmPreserved.of_vm_tpidr hvm htp (FdsHiFrame.of_fs_eq hfs), hpost⟩⟩
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

end

meta section

syntax "by_bb_vm_steps " ident tacticSeq : tactic

elab_rules : tactic
  | `(tactic| by_bb_vm_steps $h_bb:ident $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget.sepWP_rebase_bb_vmPreserved $h_bb))
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
              ``LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget.bbTrapHooks then
          some e2
        else if sub.eqv e1 then some e2
        else none
      g.assign prf2

end

@[expose] public section

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0
  and64_mask32_ite_1_0 and32_ite_1_0 and32_1_ite_1_0
  publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0
attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

noncomputable def ctEqSliceBudgetSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceSpec

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

/-! ## 3. Blocks `212`, `17`, `211`, and `28` with `VmPreserved` -/

noncomputable def publicKeyEqBudgetSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqSpec

def publicKeyEqMemBudgetSpec :
    Spec (BitVec 64 × PublicKey × BitVec 64 × PublicKey × BitVec 64) :=
  withVmPreserved publicKeyEqMemSpec

def isSameAccountBudgetSpec : Spec IsSameAccountGhost :=
  withVmPreserved isSameAccountSpec

def deserializeMemPlacedBudgetSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) :=
  withVmPreserved deserializeMemPlacedSpec

private theorem publicKey_beq_false_of_ne_ik {ik1 ik2 : IdentityKey} (h : ik1 ≠ ik2) :
    (ik1.publicKey == ik2.publicKey) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  apply h
  cases ik1
  cases ik2
  cases heq
  rfl

private theorem stackAt_isSameAccount_split_placed (sp : BitVec 64) :
    stackAt sp isSameAccountStack =
      memRegion (sp - 80#64 - 16#64) 16 ∗ memRegion (sp - 80#64 - 16#64 - 48#64) 48 ∗
      memRegion (sp - 80#64) 32 ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, isSameAccountStack]
  rw [show sp - 80#64 - 16#64 - 48#64 = sp - 144#64 by bv_omega,
      show sp - 80#64 - 16#64 = sp - 96#64 by bv_omega,
      show (80 + 64 : Nat) = 144 from rfl, show BitVec.ofNat 64 144 = 144#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 48) (k := 96) (b' := sp - 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 16) (k := 80) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 32) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (memRegion_cells (sp - 48#64) 6 (by decide) : memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]
  ac_rfl

section CalleeVmProofs
attribute [local irreducible] VmPreserved

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
      (withLsCodeLoaded lsmpl publicKeyEqMemBudgetSpec) := by
  refine subroutine_ok_map (publicKey_eq_placed_ok h_bb) ?_
  rintro ⟨p1, pk1, p2, pk2, sp⟩ R s0 hpre
  refine ⟨(p1, pk1, p2, pk2, sp), R, ?_, ?_⟩
  · simpa only [withLsCodeLoaded, publicKeyEqBudgetSpec, publicKeyEqMemBudgetSpec,
      withVmPreserved, publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpre
  · intro sf hpost
    simpa only [withLsCodeLoaded, publicKeyEqBudgetSpec, publicKeyEqMemBudgetSpec,
      withVmPreserved, publicKeyEqSpec, publicKeyEqMemSpec,
      ← memRegion_16_eq_stackFrameFor_eq sp,
      ← memRegion_48_eq_stackFrameFor_ct_eq (sp - 16#64)] using hpost

/-- Block `17` (`<IdentityKey>::is_same_account`) meets `isSameAccountBudgetSpec` under
`[LibsignalPlacement]`. -/
theorem is_same_account_placed_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_17).rebase (blkPl_17).base H) (blkPl_17).base
      (withLsCodeLoaded lsmpl isSameAccountBudgetSpec) := by
  simp only [withLsCodeLoaded, isSameAccountBudgetSpec, withVmPreserved, isSameAccountSpec,
    sepConj_assoc]
  have heq0 : subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (lsmpl.base 212)
      (withLsCodeLoaded lsmpl publicKeyEqMemBudgetSpec) :=
    publicKeyEqMem_placed_ok h_bb
  have heq := ls_subroutine_ok_of_block (callerProg := (blkPC_17).rebase (blkPl_17).base H) heq0
  simp only [withLsCodeLoaded, publicKeyEqMemBudgetSpec, withVmPreserved, publicKeyEqMemSpec,
    sepConj_assoc] at heq
  wp_init x s0
  obtain ⟨localIkA, localIk, remoteIkA, remoteIk⟩ := x
  dsimp only at *
  subst h_2 h_3
  rw [stackAt_isSameAccount_split_placed s0.sp]
  cells_unfold
  wp_pull_exists
  have hne := publicKey_beq_false_of_ne_ik h_1
  apply sepWP_seq_lscl h (mid := lsmpl.base 212)
  apply sepWP_seg_ls_vm (Q := (blkPC_17).rebase (blkPl_17).base (hooksException H))
    blkLib_eq_17 (mid := lsmpl.base 212); intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  have hvm1 : VmPreserved s0 _ := _hnsp.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm1 ⊢
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun hcl_call => ?_
  wp_apply
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at *
  apply sepWP_seg_ls_vm (Q := (blkPC_17).rebase (blkPl_17).base (hooksException H))
    blkLib_eq_17 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
  simp only [State.setMem_setMem] at hvm2 ⊢
  have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
  try simp only [sepConj_assoc, hvm_tot]
  wp_done

/-- Block `211` (`<PublicKey as TryFrom<&[u8]>>::try_from`) meets `deserializePlacedBudgetSpec`
under `[LibsignalPlacement]`. -/
theorem pkTryFrom_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      deserializePlacedBudgetSpec := by
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
  apply sepWP_seg_ls_vm (Q := (blkPC_211).rebase (blkPl_211).base (hooksException H))
    blkLib_eq_211 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip
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

/-- Block `211` (`PublicKey::try_from`) meets `deserializeMemPlacedBudgetSpec` under
`[LibsignalPlacement]`. -/
theorem pkTryFromMem_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (blkPl_211).base
      deserializeMemPlacedBudgetSpec := by
  refine subroutine_ok_map (pkTryFrom_placed_ok H) ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeMemPlacedBudgetSpec, withVmPreserved, deserializeMemPlacedSpec,
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
    simpa only [deserializePlacedBudgetSpec, deserializeMemPlacedBudgetSpec,
      withVmPreserved, deserializePlacedSpec, deserializeMemPlacedSpec, sepConj_assoc]
      using hpost

end CalleeVmProofs

/-- Block `28` (`<SessionState>::local_identity_key`) meets `Getters.DefsBudget.localIdentityKeyPlacedSpec A`
under `[LibsignalPlacement]` (re-exported from `Getters.IdentityBudget`). -/
abbrev local_identity_key_placed_ok :=
  @LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget.local_identity_key_placed_ok

/-! ## 4. Relocatable Block `130` `reaches_pc` Step Lemmas with `VmPreserved` -/

theorem identityKeys_step1_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (h_pc : s0.pc = (blkPl_131).base)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA) (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA) (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hm : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 84#64) s0
      (fun s1 => VmPreserved s0 s1 ∧ s1.sp = sp ∧ s1.spAligned = true ∧
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = sp + 320#64 ∧
        s1.readReg64 .x21 = x.ss ∧ s1.readReg64 .x22 = x.msgA ∧
        s1.readReg64 .x23 = sp + 1280#64 ∧ (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s1.readReg64 .x25 = x.locA ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.mem ⊨ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
          vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r10_11, w_sp0, w_sp48, hm1⟩ :=
    identityKeys_prologue_extract hm
  have hm_pre : s0.mem ⊨
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r10_11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack) ∗
      (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ F) := by
    dsimp only [sp] at hm1 ⊢; convert hm1 using 1; sep_ac_rfl
  have hlocal := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (local_identity_key_placed_ok A H)
  have hwp := identityKeys_prologue_wp_placed hlocal x s0 hcl r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r10_11
    w_sp0 w_sp48 h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s1 _ _ ⟨P_f, hm_s1, hvm, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, hPf⟩
  refine ⟨hvm, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s1
  have h48 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40 ⊢ memRegion sp 48 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion sp 0#64)) ?_
    rw [← memRegion_split sp 8 40 (by decide)]; exact Entails.refl _
  have hm3 : s1.mem ⊨
      ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40) ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp localIdentityKeyStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) ∗
       tryDecryptSavedRegs s0.sp s0 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp localIdentityKeyStack (by decide)] at hm3
  have hm4 := Satisfies.mono (sepConj_mono_left h48) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step2_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s1 : State)
    (h_pc : s1.pc = (blkPl_131).base + 84#64) (h_run : s1.status = .Running)
    (h_sp : s1.sp = s0.sp - 1504#64) (h_sp_align : s1.spAligned = true)
    (htr : s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx19 : s1.readReg64 .x19 = x.ret) (hx20 : s1.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s1.readReg64 .x21 = x.ss) (hx22 : s1.readReg64 .x22 = x.msgA)
    (hx23 : s1.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s1.readReg64 .x25 = x.locA) (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hm : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 156#64) s1
      (fun s2 => VmPreserved s1 s2 ∧ s2.sp = sp ∧ s2.spAligned = true ∧
        (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.readReg64 .x0 = x.ss ∧ s2.readReg64 .x8 = sp + 400#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = sp + 320#64 ∧
        s2.readReg64 .x21 = x.ss ∧ s2.readReg64 .x22 = x.msgA ∧
        s2.readReg64 .x23 = sp + 1280#64 ∧ (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s2.readReg64 .x25 = x.locA ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        (s2.mem ⊨ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          memRegion (sp + 1312#64) 96 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hx29' : s1.readReg64 .x29 = sp + 1408#64 := by rw [hx29]; dsimp only [sp]; bv_omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, hloc_eq⟩ :=
    exists_localGroupA_of_length_32 (List.Vector.toList_length x.st.localIdentity.publicKey.bytes)
  have hm_433 : s1.mem ⊨ memRegion (sp + 433#64) 975 ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, hm_ext⟩ :=
    identityKeys_step2_extract hm_433
  unfold localIdentityOkAt at hm_ext
  rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, hloc_eq (sp + 401#64)] at hm_ext
  have hm_pre : s1.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112)) ∗
      (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hwp := identityKeys_copy_local_ik_wp_placed (H := H) x s0 s1 b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31
    d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 u1104 u1112 h_pc h_run h_sp h_sp_align hx20 hx21 hx23 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s2 _ _ ⟨P_f, hm_s2, hvm2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hPf⟩
  refine ⟨hvm2, hsp2, halign2, by reg_chain, hx0_2, hx8_2, by reg_chain, hx20_2, hx21_2,
    by reg_chain, hx23_2, by reg_chain, by reg_chain, by rw [hx29_2]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s2
  rw [← localGroupA_eq_localGroupB, ← localGroupA_eq_localGroupB,
      ← hloc_eq (sp + 401#64), ← hloc_eq (sp + 1280#64)] at hm2
  have hm3 : s2.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ∗
      (memRegion (sp + 56#64) 344 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  have hm4 := Satisfies.mono (sepConj_mono_left (identityKeys_step2_recombine sp x.st.localIdentity w2 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_step3_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrem : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 29)
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (F : SepProp) (s0 s2 : State)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (h_pc : s2.pc = (blkPl_131).base + 156#64) (h_run : s2.status = .Running)
    (h_sp : s2.sp = s0.sp - 1504#64) (h_sp_align : s2.spAligned = true)
    (htr : s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx0 : s2.readReg64 .x0 = x.ss) (hx8 : s2.readReg64 .x8 = (s0.sp - 1504#64) + 400#64)
    (hx19 : s2.readReg64 .x19 = x.ret) (hx20 : s2.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s2.readReg64 .x21 = x.ss) (hx22 : s2.readReg64 .x22 = x.msgA)
    (hx23 : s2.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s2.readReg64 .x25 = x.locA) (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hm : s2.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 160#64) s2
      (fun s3 => VmPreserved s2 s3 ∧ s3.sp = sp ∧ s3.spAligned = true ∧
        (s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) ∧
        s3.readReg64 .x19 = x.ret ∧ s3.readReg64 .x20 = sp + 320#64 ∧
        s3.readReg64 .x21 = x.ss ∧ s3.readReg64 .x22 = x.msgA ∧
        s3.readReg64 .x23 = sp + 1280#64 ∧ (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s3.readReg64 .x25 = x.locA ∧ s3.readReg64 .x29 = s0.sp - 96#64 ∧
        (s3.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗
          remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)] at hm
  have hm_pre : s2.mem ⊨
      (vecGhostAt A x.G.remoteIk (x.ss + 0x18#64) ∗ memRegion (s2.sp + 400#64) 34 ∗
       logOff tryDecryptDummyImg ∗ stackAt s2.sp remoteIdentityKeyStack) ∗
      (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - remoteIdentityKeyStack) ∗ F) := by
    rw [h_sp]; convert hm using 1; sep_ac_rfl
  have hx8' : s2.readReg64 .x8 = s2.sp + 400#64 := by rw [h_sp]; exact hx8
  have hwp := identityKeys_call_remote_ik_wp_placed hrem x s2 hcl h_pc h_run h_sp_align hx0 hx8' hdeser_rem
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s3 _ _ ⟨P_f, hm_s3, hvm3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hPf⟩
  refine ⟨hvm3, by reg_chain, halign3, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s3; rw [h_sp] at hm2
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)]
  convert hm2 using 1; sep_ac_rfl

theorem identityKeys_step4_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (tag : BitVec 8) (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s3.pc = (blkPl_131).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hent_402 : remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
      memRegion ((s0.sp - 1504#64) + 402#64) 32)
    (hm : s3.mem ⊨ ((s0.sp - 1504#64 + 400#64) ↦₈ 0#8) ∗ ((s0.sp - 1504#64 + 401#64) ↦₈ tag) ∗
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 384#64) s3
      (fun s4 => VmPreserved s3 s4 ∧ s4.sp = sp ∧ s4.spAligned = true ∧
        (s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) ∧
        s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        s4.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧ s4.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        s4.readReg64 .x19 = x.ret ∧ s4.readReg64 .x20 = sp + 320#64 ∧
        s4.readReg64 .x21 = x.ss ∧ s4.readReg64 .x22 = x.msgA ∧
        s4.readReg64 .x23 = sp + 1280#64 ∧ (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s4.readReg64 .x25 = x.locA ∧ s4.readReg64 .x29 = s0.sp - 96#64 ∧
        (s4.mem ⊨ memRegion (sp + 400#64) 34 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
          ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
          memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
          memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hm_sub : s3.mem ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u352, u360, u976, u980, u981, hm_ext⟩ := identityKeys_step4_extract hm_sub
  have hm_pre : s3.mem ⊨
      (((s3.sp + 400#64) ↦₈ 0#8) ∗ ((s3.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s3.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s3.sp + 352#64) ↦₆₄ u352) ∗ ((s3.sp + 360#64) ↦₈ u360) ∗
       ((s3.sp + 976#64) ↦₃₂ u976) ∗ ((s3.sp + 980#64) ↦₈ u980) ∗ ((s3.sp + 981#64) ↦₈ u981)) ∗
      (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s3.readReg64 .x20 = s3.sp + 320#64 := by rw [h_sp]; exact hx20
  have hwp := identityKeys_remote_ik_common_wp_placed (H := H) s3 tag w0 b4 b5 b6 b7 b8 b9 b10 b11
    b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 u352 u360 u976 u980 u981
    h_pc h_run h_sp_align hx20'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s4 _ _ ⟨P_f, hm_s4, hvm4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hPf⟩
  refine ⟨hvm4, by reg_chain, halign4, by reg_chain, hx8_4, hx9_4, hx10_4, hx11_4,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s4; rw [h_sp] at hm2
  have h400_34 :
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 401#64) tag) hent_402)) ?_
    rw [show sp + 402#64 = (sp + 401#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 1 32 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]; exact Entails.refl _
  have hm3 : s4.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ∗
      (((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  exact Satisfies.mono (sepConj_mono_left h400_34) hm3

theorem identityKeys_step5_none_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s4 : State)
    (h_pc : s4.pc = (blkPl_131).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx11 : s4.readReg64 .x11 = 0#64) (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA) (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hm : s4.mem ⊨ memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s4
      (fun s5 => VmPreserved s4 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ memRegion (sp + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [memRegion_split (sp + 56#64) 968 384 (by decide), show sp + 56#64 + 968#64 = sp + 1024#64 by bv_omega,
      memRegion_split (sp + 1024#64) 8 376 (by decide), show sp + 1024#64 + 8#64 = sp + 1032#64 by bv_omega,
      memRegion_split (sp + 1032#64) 8 368 (by decide), show sp + 1032#64 + 8#64 = sp + 1040#64 by bv_omega,
      memRegion_split (sp + 1040#64) 240 128 (by decide), show sp + 1040#64 + 240#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 8 120 (by decide), show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm
  have hm1 : s4.mem ⊨ memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 8 ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u1024, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : s4.mem ⊨ memRegion (sp + 1032#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1032, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : s4.mem ⊨ memRegion (sp + 1280#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ ((sp + 1032#64) ↦₆₄ u1032) ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1280, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm_pre : s4.mem ⊨
      (((s4.sp + 1024#64) ↦₆₄ u1024) ∗ ((s4.sp + 1032#64) ↦₆₄ u1032) ∗ ((s4.sp + 1280#64) ↦₆₄ u1280) ∗ logOff tryDecryptDummyImg) ∗
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm3 ⊢; convert hm3 using 1; sep_ac_rfl
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hwp := identityKeys_remote_none_wp_placed (H := H) s4 u1024 u1032 u1280 h_pc h_run h_sp_align hx11 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hvm5, by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm4 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm4
  have hm5 : s5.mem ⊨
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1024#64) 16 ∗ memRegion (sp + 1040#64) 240 ∗
       memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 120) ∗ (logOff tryDecryptDummyImg ∗ F) := by
    dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
  rw [show sp + 1288#64 = (sp + 1280#64) + 8#64 by bv_omega, ← memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 = (sp + 1040#64) + 240#64 by bv_omega, ← memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 = (sp + 1024#64) + 16#64 by bv_omega, ← memRegion_split (sp + 1024#64) 16 368 (by decide),
      show sp + 1024#64 = (sp + 56#64) + 968#64 by bv_omega, ← memRegion_split (sp + 56#64) 968 384 (by decide)] at hm5
  exact hm5

end

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget
