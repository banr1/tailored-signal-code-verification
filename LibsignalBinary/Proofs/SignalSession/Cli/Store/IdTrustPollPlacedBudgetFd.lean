/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudgetFd
import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<IdentityFiles as IdentityKeyStore>::is_trusted_identity::{closure#0}`

Lifts `PublicKey::try_from` (Block 211), `<PublicKey as PartialEq>::eq` (Block 212), and
`IdentityKey::decode` (Block 18) to `.keepsFs` / `withFdsGe3Closed`, and proves
`withFdsGe3Closed (idTrustPollSpecPlaced …)` on Block `566`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_eq_212 blkPC_212 blkPC_213 blkPl_212 blkPl_213 libsignalMutatedBlocks lsBlackBoxU8Sym
   lsLogFilterAddr ls_externAt?_of_mem ls_subroutine_ok_cl_of_plain ls_subroutine_ok_of_block lsmpl
   lsρ sepWP_seq_lscl subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (and32_1_ite_1_0 and32_ite_1_0 and64_1_ite_1_0 and64_ite_1_0 and64_mask255_ite_1_0
   and64_mask32_ite_1_0 byte_bne_zext32 csinc_eq_zero32_ite_1_0 ctEqSliceSpec ct_eq_bool_32
   ite_bne_byte_0_1 pointsToBytes32 pointsToBytes_eq_pointsToBytes32 publicKey_bytes_toList_length
   publicKey_ite_toList_eq setWidth32_ite_1_0 setWidth64_ite_1_0_32 setWidth64_ite_1_0_8
   setWidth8_ite_1_0 stackFrameFor_ctEq_eq_cells_ext32)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack lsLogOff pkTryFromPlacedSpec pkTryFromResultAt pkTryFromSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (speAt)
open CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom
  (badLen_pre_weaken memRegion_40_split_badLen memRegion_40_split_badType
   memRegion_40_split_nil memRegion_40_split_ok nil_pre_weaken pointsToBytes_ok_split
   publicKey_deserialize_badKeyLength publicKey_deserialize_badKeyType
   publicKey_deserialize_nil publicKey_deserialize_ok_of_ge32
   ult_sub_of_ge33 ult_sub_of_lt32)
open CryptoVerification.LibsignalTripleRatchet.Getters
  (blkLib_eq_211 blkPC_211 blkPl_211 publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed (blkLib_eq_18 blkPC_18 blkPl_18 lsProg_18)
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyResultAt)
open CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.Helpers
  (exists_ikKeyChunks_of_length_32 ikKeyChunks_ret_8 ikKeyChunks_sp_87 mask_split_64
   memRegion_48_err_split memRegion_48_ok_split memRegion_sp_88_badLen_post
   memRegion_sp_88_badType_post memRegion_sp_88_nil_post memRegion_sp_88_ok_post
   pkTryFrom_sp_88_badLen pkTryFrom_sp_88_badType pkTryFrom_sp_88_nil pkTryFrom_sp_88_ok
   pointsTo64_zext8_split publicKey_deserialize_cases sevenLo_ret_8 sevenLo_sp_87 sp_88_repack
   spe_badKeyType_post spe_noKeyType_post stackAt_ikDec_split truncate16_zeroExtend32
   truncate8_zeroExtend32 zero_orr_zext8_mask)
open CryptoVerification.SignalSession.Cli (DirGhost IdPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_566)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_cl_to_lscro)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
  (bbTrapHooks ctEqSliceBudgetSpec publicKeyEqBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (pkTryFromPlacedBudgetSpec)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro subroutine_ok_withFdsGe3Closed_of_keepsFs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced idTrustPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (CliIdTrustPollEnv identityKeyDecodePlacedBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.SymPlacedBudgetFd
  (idTrustPollInner_env_placed_ok_fd idTrustPollInner_placed_ok_fd idTrustPoll_placed_of_inner_fd)

section Placed

/-! ## 1. `.keepsFs` / `withFdsGe3Closed` Lifts for Blocks `211`, `213`, `212`, and `18` -/

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

private theorem steps_rebase_bbTrapHooks_noSyscalls_fs {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    {s sm : State}
    (hsteps : Steps ((P.rebase b bbTrapHooks).withSvc noSyscalls) s sm)
    (hrun_m : sm.status = .Running) :
    Steps (P.rebase b Hk) s sm ∧ sm.fs = s.fs ∧ ProofLib.StdStartup.VmFieldsPreserved s sm := by
  induction hsteps with
  | refl => exact ⟨Steps.refl _, rfl, ProofLib.StdStartup.VmFieldsPreserved.refl _⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_m
      | step hs _ => cases hs <;> assumption
    rcases ih hrun_m with ⟨hsteps_rest, hfs_rest, hvm_rest⟩
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern_fault _ _ _ => cases s1; cases hr2
    | extern hr1 hext hkeep hsym =>
      rcases externAt?_rebase_bbTrapHooks_some h_bb hext with rfl | ⟨rfl, hext_hk⟩
      · cases s1; cases hr2
      · have hvm_bb : ProofLib.StdStartup.VmFieldsPreserved s1 (blackBoxHook s1) :=
          ⟨rfl, rfl, rfl, fun _ => rfl⟩
        exact ⟨Steps.step (Step.extern hr1 hext_hk hkeep hsym) hsteps_rest,
          hfs_rest, ProofLib.StdStartup.VmFieldsPreserved.trans hvm_bb hvm_rest⟩
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
      have hfs1 : (execInst inst s1).fs = s1.fs :=
        (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2
      rw [hev1] at hsteps_rest hfs_rest hvm_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        hfs_rest.trans hfs1,
        ProofLib.StdStartup.VmFieldsPreserved.trans
          (ProofLib.StdStartup.execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest⟩

private theorem sepWP_rebase_bb_vmPreserved_fs {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)} (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b bbTrapHooks).withSvc noSyscalls) target_pc s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ post sm Pm)) :
    SepWP (P.rebase b Hk) target_pc s Pre
      (fun sm Pm => sm.fs = s.fs ∧ VmPreserved s sm ∧ post sm Pm) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  have hL' : ((P.rebase b bbTrapHooks).withSvc noSyscalls).CodeLoaded s.mem :=
    hL.of_base_code rfl rfl
  obtain ⟨sm, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL'
  rcases hout with ⟨hpc, hrun, Pm, hPm, htp, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_hk, hfs, hvm⟩ := steps_rebase_bbTrapHooks_noSyscalls_fs h_bb hsteps hrun
    exact ⟨sm, hsteps_hk, Or.inl ⟨hpc, hrun, Pm, hPm, hfs,
      VmPreserved.of_vm_tpidr hvm htp (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs), hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem externAt?_bbTrapHooks_213 [LibsignalPlacement] :
    ((blkPC_213).rebase (blkPl_213).base bbTrapHooks).externAt?
      (lsρ lsBlackBoxU8Sym) = some blackBoxHook :=
  (ls_externAt?_of_mem (H := bbTrapHooks)).trans (by simp [bbTrapHooks])

private theorem subroutine_ok_withVmPreserved_keepsFs_intro {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => sf.fs = s0.fs ∧ VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec).keepsFs := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hfs, hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [Spec.keepsFs, withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hfs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

local syntax "by_bb_vm_steps_fs " ident tacticSeq : tactic

local elab_rules : tactic
  | `(tactic| by_bb_vm_steps_fs $h_bb:ident $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply sepWP_rebase_bb_vmPreserved_fs $h_bb))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
        throwError "by_bb_vm_steps_fs: expected `SepWP`, got{Lean.indentExpr ty}"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_bb_vm_steps_fs: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_bb_vm_steps_fs: inner tactic left {rem.length} unsolved goal(s)"
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

section CtEq

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp]
  byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0
  and64_mask32_ite_1_0 and32_ite_1_0 and32_1_ite_1_0
  publicKey_bytes_toList_length and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0
attribute [local simp, local wp_norm, local arm64_norm] Bool.and_assoc

set_option maxHeartbeats 1600000 in
private theorem ct_eq_placed_ok_keepsFs [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceBudgetSpec.keepsFs := by
  have hext : ((blkPC_213).rebase (blkPl_213).base bbTrapHooks).externAt?
      (lsρ lsBlackBoxU8Sym) = some blackBoxHook := externAt?_bbTrapHooks_213
  apply subroutine_ok_withVmPreserved_keepsFs_intro
  intro x R s0 hpc hrun hpre hsp_align
  clear hpre
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  unfold State.spAligned at hsp_align
  dsimp only [ctEqSliceSpec, Reg.x0, Reg.x1, Reg.x30, Reg.lr] at *
  simp only [sepConj_assoc]
  by_bb_vm_steps_fs h_bb (
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

end CtEq

attribute [local irreducible] Program.fetch Program.externAt? VmPreserved

/-- `.keepsFs`-strengthened `<PublicKey as PartialEq>::eq` (Block `212`). -/
theorem publicKeyEq_placed_ok_of_bb_keepsFs [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H)
      (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)).keepsFs := by
  have hct0 : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      ctEqSliceBudgetSpec.keepsFs := ct_eq_placed_ok_keepsFs h_bb
  have hct := ls_subroutine_ok_of_block (callerProg := (blkPC_212).rebase (blkPl_212).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hct0)
  simp only [withLsCodeLoaded, Spec.keepsFs, ctEqSliceBudgetSpec, withVmPreserved, ctEqSliceSpec,
    sepConj_assoc] at hct
  change subroutine_ok ((blkPC_212).rebase (blkPl_212).base H) (blkPl_212).base
    (withLsCodeLoaded lsmpl publicKeyEqBudgetSpec).keepsFs
  simp only [withLsCodeLoaded, Spec.keepsFs, publicKeyEqBudgetSpec, withVmPreserved,
    publicKeyEqSpec, sepConj_assoc]
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
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _hcl_call => ?_
  wp_apply
  rw [publicKey_ite_toList_eq] at *
  apply sepWP_seg_ls_vm (Q := (blkPC_212).rebase (blkPl_212).base (hooksException H))
    blkLib_eq_212 (mid := s0.readReg64 (Reg.gpr 30#5)); intro _m_strip2
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
  have hfs2 := _hnsp2.2.2.2.2.2.2
  simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
  have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
  have hfs_tot := hfs2.trans (by assumption : _ = s0.fs)
  try simp only [sepConj_assoc, hvm_tot, hfs_tot, *]
  wp_done

/-- `withFdsGe3Closed`-threaded `<PublicKey as PartialEq>::eq` (Block `212`). -/
theorem publicKeyEq_placed_ok_of_bb_fd [LibsignalPlacement] {H : LibsignalHooks}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_212).rebase (blkPl_212).base H)
      (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs (publicKeyEq_placed_ok_of_bb_keepsFs h_bb)

set_option maxHeartbeats 1600000 in
/-- `.keepsFs`-strengthened `<PublicKey as TryFrom<&[u8]>>::try_from` (Block `211`). -/
theorem pkTryFrom_placed_ok_keepsFs [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedBudgetSpec.keepsFs := by
  simp only [Spec.keepsFs, pkTryFromPlacedBudgetSpec, withVmPreserved, pkTryFromPlacedSpec,
    pkTryFromSpec, lsLogOff, sepConj_assoc]
  wp_init g s0
  obtain ⟨ptr, bs, out⟩ := g
  dsimp only at *
  subst h_1 h
  apply sepWP_seg_ls_vm (Q := (blkPC_211).rebase (blkPl_211).base (hooksException H))
    blkLib_eq_211 (mid := s0.readReg64 (Reg.gpr 30#5))
  intro _m_strip
  rcases bs with _ | ⟨b0, rest⟩
  · have hx1 : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simpa using h_2
    rw [publicKey_deserialize_nil, pkTryFromResultAt,
      memRegion_40_split_nil (s0.readReg64 (Reg.gpr 8#5))]
    wp_pull_exists
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
    have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
    have hfs := hnsp.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm hfs ⊢
    refine SepWP.weaken_pre
      (nil_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
        lsLogFilterAddr) ?_
    simp only [sepConj_assoc, *]
    wp_done
  · have hx1_ne : s0.readReg64 (Reg.gpr 1#5) ≠ 0#64 := by
      intro heq; rw [heq] at h_2; simp at h_2
    by_cases hb0 : b0 = 5#8
    · subst hb0
      by_cases hlen : rest.length < 32
      · have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = true :=
          ult_sub_of_lt32 (by simp only [List.length_cons] at h_2; omega)
            (by simp only [List.length_cons] at h_2; omega)
        rw [publicKey_deserialize_badKeyLength rest hlen, pkTryFromResultAt,
          pointsToBytes_cons, memRegion_40_split_badLen (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        wp_steps
        refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
        have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
        have hfs := hnsp.2.2.2.2.2.2
        simp only [State.setMem_setMem] at hvm hfs ⊢
        have hx1_eq : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (rest.length + 1) := by
          apply BitVec.eq_of_toNat_eq
          simp only [List.length_cons] at h_2
          rw [h_2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hx1_eq] at hvm hfs ⊢
        refine SepWP.weaken_pre
          (badLen_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) (s0.readReg64 (Reg.gpr 8#5))
            (BitVec.ofNat 64 (rest.length + 1)) lsLogFilterAddr rest) ?_
        try simp only [sepConj_assoc, *]
        wp_done
      · have hge32 : 32 ≤ rest.length := by omega
        have hult : (s0.readReg64 (Reg.gpr 1#5) - 1#64).ult
            (s0.readReg64 (Reg.gpr 1#5) - 33#64) = false :=
          ult_sub_of_ge33 (by simp only [List.length_cons] at h_2; omega)
        obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ :=
          exists_unpack64_of_length_32 (bs := rest.take 32)
            (by simp [List.length_take, Nat.min_eq_left hge32])
        rw [publicKey_deserialize_ok_of_ge32 rest hge32, pkTryFromResultAt]
        simp only [List.Vector.toList_mk, Reg.x8]
        rw [pointsToBytes_ok_split (s0.readReg64 (Reg.gpr 0#5)) hge32,
          hpk_cells (s0.readReg64 (Reg.gpr 0#5) + 1#64),
          memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
        wp_pull_exists
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        wp_steps
        wp_if hcbz9
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          have hfs := hnsp.2.2.2.2.2.2
          simp only [State.setMem_setMem] at hvm hfs ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
        · wp_steps
          refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
          have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
          have hfs := hnsp.2.2.2.2.2.2
          simp only [State.setMem_setMem] at hvm hfs ⊢
          rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, *]
          wp_done
    · rw [publicKey_deserialize_badKeyType rest hb0, pkTryFromResultAt,
        pointsToBytes_cons, memRegion_40_split_badType (s0.readReg64 (Reg.gpr 8#5))]
      wp_pull_exists
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real hnsp => ?_
      have hvm : VmPreserved s0 _ := hnsp.toVmPreserved (by wp_norm_lhs)
      have hfs := hnsp.2.2.2.2.2.2
      simp only [State.setMem_setMem] at hvm hfs ⊢
      try simp only [sepConj_assoc, *]
      wp_done

set_option maxHeartbeats 1200000 in
/-- `.keepsFs`-strengthened `IdentityKey::decode` (Block `18`) from `pkTryFromPlacedBudgetSpec.keepsFs`. -/
theorem identityKey_decode_placed_ok_of_pkTryFrom_keepsFs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hpk : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedBudgetSpec.keepsFs) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedBudgetSpec A).keepsFs := by
  have hcall : subroutine_ok (lsProg_18 H) (lsmpl.base 211)
      (withLsCl lsmpl pkTryFromPlacedBudgetSpec.keepsFs) :=
    ls_subroutine_ok_cl_of_plain (callerProg := lsProg_18 H) hpk
  clear hpk
  simp only [withLsCl, Spec.keepsFs, pkTryFromPlacedBudgetSpec, withVmPreserved,
    pkTryFromPlacedSpec, pkTryFromSpec, sepConj_assoc] at hcall
  simp only [Spec.keepsFs, identityKeyDecodePlacedBudgetSpec, withLsCodeLoaded, withVmPreserved,
    identityKeyDecodeRawSpec, sepConj_assoc]
  wp_init x s0
  obtain ⟨bytesA, bytes, ret⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = bytesA := by assumption
  have hx8 : s0.readReg64 (Reg.gpr 8#5) = ret := by assumption
  subst hx0 hx8
  rcases publicKey_deserialize_cases bytes with
    ⟨pk, hdes, hdec⟩ | ⟨hdes, hdec⟩ | ⟨t, hdes, hdec⟩ | ⟨n, hdes, hdec⟩
  · have hbs32 : pk.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_ikKeyChunks_of_length_32 hbs32
    rw [hdec, memRegion_48_ok_split (s0.readReg64 (Reg.gpr 8#5)),
        identityKeyResultAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
        ikKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_ok_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_ok s0.sp pk, hchunks (s0.sp - 87#64), ikKeyChunks_sp_87 s0.sp]
    simp only [sepConj_assoc]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    rw [sevenLo_sp_87 s0.sp]
    wp_steps
    rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_steps
    rw [sp_88_repack s0.sp]
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 := _hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    have hfs_tot := hfs2.trans (by assumption : _ = s0.fs)
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    try simp only [sepConj_assoc, hvm_tot, hfs_tot, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_noKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_nil_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 := _hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    have hfs_tot := hfs2.trans (by assumption : _ = s0.fs)
    try simp only [sepConj_assoc, hvm_tot, hfs_tot, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_badKeyType_post A.repAlloc (s0.readReg64 (Reg.gpr 8#5)) t]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badType_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 := _hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    have hfs_tot := hfs2.trans (by assumption : _ = s0.fs)
    try rw [zero_orr_zext8_mask]
    rw [pointsTo64_zext8_split (s0.readReg64 (Reg.gpr 8#5)) t]
    try simp only [sepConj_assoc, hvm_tot, hfs_tot, *]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badLen_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 211)
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := lsmpl.base 211)
    intro _m_strip1
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
    have hvm1 : VmPreserved s0 _ := _hnsp1.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm1 ⊢
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    intro _hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    apply sepWP_seg_ls_vm (Q := (blkPC_18).rebase (blkPl_18).base (hooksException H))
      blkLib_eq_18 (mid := s0.readReg64 (Reg.gpr 30#5))
    intro _m_strip2
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    have hvm2 : VmPreserved _ _ := _hnsp2.toVmPreserved (by wp_norm_lhs)
    have hfs2 := _hnsp2.2.2.2.2.2.2
    simp only [State.setMem_setMem] at hvm2 hfs2 ⊢
    try rw [mask_split_64] at hvm2 hfs2 ⊢
    have hvm_tot : VmPreserved s0 _ := hvm1.trans ((by assumption : VmPreserved _ _).trans hvm2)
    have hfs_tot := hfs2.trans (by assumption : _ = s0.fs)
    dsimp only [identityKeyResultAt, speAt]
    try simp only [sepConj_assoc, hvm_tot, hfs_tot, *]
    wp_done

/-- `.keepsFs`-strengthened `IdentityKey::decode` (Block `18`) for any hooks `H`. -/
theorem identityKey_decode_placed_ok_keepsFs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedBudgetSpec A).keepsFs :=
  identityKey_decode_placed_ok_of_pkTryFrom_keepsFs (pkTryFrom_placed_ok_keepsFs H)

/-- `withFdsGe3Closed`-threaded `IdentityKey::decode` (Block `18`) for any hooks `H`. -/
theorem identityKey_decode_placed_ok_fd [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)) :=
  subroutine_ok_withFdsGe3Closed_of_keepsFs (identityKey_decode_placed_ok_keepsFs H)

/-- Commute `withFdsGe3Closed` inside `withLsCodeLoaded` and transfer to `withLsCodeRoLoaded`. -/
theorem ls_transfer_withFdsGe3Closed_cl_to_lscro [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok calleeProg entry (withFdsGe3Closed (withLsCodeLoaded lsmpl spec)))
    (hi : i < 619 := by decide)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCodeRoLoaded lsmpl (withFdsGe3Closed spec)) := by
  have hcl : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl (withFdsGe3Closed spec)) :=
    subroutine_ok_mono h
      (fun _ _ _ hp => by
        dsimp only [withLsCodeLoaded, withFdsGe3Closed] at hp ⊢
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp)
      (fun _ _ _ _ hq => hq)
  exact ls_transfer_cl_to_lscro (callerProg := callerProg) (calleeProg := calleeProg)
    (i := i) (j := j) hcl hi hj hj_unmut

/-! ## 2. Block `566` (`is_trusted_identity::{closure#0}`) Entry Theorems with `withFdsGe3Closed` -/

theorem idTrustPoll_placed_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk)) := by
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner_fd
    (fun hhi => idTrustPollInner_placed_ok_fd hFs hGet' hDec' hEq'
      hFitGet hTrustGet hTrustGetFree hhi) hstk

/-- Block `566` (`is_trusted_identity::{closure#0}`) meets two-sided
`withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)`
given `AllocContractsFsPlaced`, `withFdsGe3Closed (dirGetSpecPlaced …)` (block `589`),
`IdentityKey::decode` (block `18`), and `<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idTrustPoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg decProg eqProg : Program} {getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) := by
  have hGet' := ls_transfer_withFdsGe3Closed_lscro (callerProg := lsProg_566 H)
    hGet (by decide) hGetBlk hGetUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro (callerProg := lsProg_566 H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idTrustPoll_placed_of_inner_fd
    (fun hhi => idTrustPollInner_env_placed_ok_fd hFs hGet' hDec' hEq' hhi) hstk

/-- Convenience specialization discharging `IdentityKey::decode` via
`identityKey_decode_placed_ok_fd` and `<PublicKey as PartialEq>::eq` via
`publicKeyEq_placed_ok_of_bb_fd`. -/
theorem idTrustPoll_placed_ok_of_get_bb_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {getProg : Program} {getBlk : Nat} [IsLsBlockProg getProg getBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_566 H) (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) :=
  idTrustPoll_placed_ok_of_deps_fd hFs hGet
    (identityKey_decode_placed_ok_fd H)
    (publicKeyEq_placed_ok_of_bb_fd h_bb) hstk hGetBlk hGetUnmut

theorem idTrustPoll_placed_caller_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {TrustEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hFitGet : ∀ F0 x st, FitsEnv M lim st (TrustEnv F0 x) →
      FitsEnv M lim st (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hTrustGet : ∀ F0 x evs, GetEnv F0 x.peers x.call.call.addr.name.bytes evs →
      TrustEnv F0 x evs)
    (hTrustGetFree : ∀ F0 x evs₁ evs₂,
      GetEnv F0 x.peers x.call.call.addr.name.bytes evs₁ → FreeOnlyEvs evs₂ →
      TrustEnv F0 x (evs₁ ++ evs₂))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim TrustEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps_gen_fd hFs hGet hDec hEq
      hFitGet hTrustGet hTrustGetFree hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

theorem idTrustPoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg decProg eqProg : Program}
    {callerBlk getBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hstk : 192 + max (max getStk 96) (max 64 extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 566)
      (withFdsGe3Closed (idTrustPollSpecPlaced rd pathOk A lim (CliIdTrustPollEnv GetEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 566)
    (idTrustPoll_placed_ok_of_deps_fd hFs hGet hDec hEq hstk
      hGetBlk hGetUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
