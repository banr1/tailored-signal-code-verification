/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlaced
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEq
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.OpcodeExclusion
import ProofLib.SepLogic.WP.Apply
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# `VmPreserved` Lockstep Bridges for `ct_eq` (Block `213`) and `expand_multi_info` (Block `53`)

Proves `ct_eq_ro_placed_vm_ok` (Block `213`) and `expand_multi_info_placed_vm_ok` (Block `53`) with
`VmPreserved` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAux

open Arm64 ProofLib SepProp BitVec
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_213 blkPl_213 libsignalSessionLib
   lsBlackBoxU8Sym ls_externAt?_blockProgram_eq_of_externs_eq ls_externAt?_of_mem
   lsmpl lsρ prog_eq_blockProgram withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (and32_1_ite_1_0 and32_ite_1_0 and64_1_ite_1_0 and64_ite_1_0 and64_mask32_ite_1_0
   byte_bne_zext32 ct_eq_bool_32 ite_bne_byte_0_1 pointsToBytes32
   pointsToBytes_eq_pointsToBytes32 setWidth32_ite_1_0 setWidth64_ite_1_0_32
   setWidth64_ite_1_0_8 setWidth8_ite_1_0)
open scoped CryptoVerification.LibsignalSession.FindReceiverChainIndex
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HkdfPlacedHooks RunsTo TraceEq
   blkLib_123 blkLib_53 blkLib_eq_123 blkLib_eq_53 blkPC_123 blkPC_53 blkPl_123 blkPl_53
   ctEqSliceROSpec expPlacedFakeB expPlacedFakeB_off_0 expandMultiInfoSpec
   hmacCoreAt isBlock_hmacCoreAt
   lsCompress256Sym lsMemcpySym lsMemsetSym ro_outside_rw_shared_lb)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
  (pointsToBytesRO32 pointsToBytesRO_eq_pointsToBytesRO32)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandFrame ExpandPost ExpandPre KeepsFrozenNoAnon
   expand_multi_info_placed_runsTo_of_fin
   hkdfExpand_64_eq hkdfExpand_80_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof
  (finalize_fixed_placed_runsTo)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC vmPreserved_writeReg64)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm placedLib_rebase_allInstrs_safeVm stripS_calleeSavedVRegs
   stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)

/-! ## 1. Relocatable `ct_eq` with `VmPreserved` (Block `213`) -/

private def VmNoTpidr (s₁ s₂ : State) : Prop :=
  (s₂.brkStart = s₁.brkStart ∧ s₂.brk = s₁.brk) ∧
  s₂.physMemAvail = s₁.physMemAvail ∧
  (∀ a, s₂.mem.perm a = s₁.mem.perm a) ∧
  LibsignalBinary.Heap.FdsHiFrame s₁ s₂

private theorem VmNoTpidr.refl (s : State) : VmNoTpidr s s :=
  ⟨⟨rfl, rfl⟩, rfl, fun _ => rfl, LibsignalBinary.Heap.FdsHiFrame.refl s⟩

private theorem VmNoTpidr.trans {s₁ s₂ s₃ : State}
    (h₁₂ : VmNoTpidr s₁ s₂) (h₂₃ : VmNoTpidr s₂ s₃) : VmNoTpidr s₁ s₃ :=
  ⟨⟨h₂₃.1.1.trans h₁₂.1.1, h₂₃.1.2.trans h₁₂.1.2⟩,
   h₂₃.2.1.trans h₁₂.2.1,
   fun a => (h₂₃.2.2.1 a).trans (h₁₂.2.2.1 a),
   h₁₂.2.2.2.trans h₂₃.2.2.2⟩

private theorem VmNoTpidr.toVmPreserved {s₁ s₂ : State}
    (h : VmNoTpidr s₁ s₂) (htp : s₂.tpidrEl0 = s₁.tpidrEl0) : VmPreserved s₁ s₂ :=
  ⟨⟨h.1.1, h.1.2, htp⟩, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem vmNoTpidr_blackBoxHook (s : State) : VmNoTpidr s (blackBoxHook s) := by
  have hv : VmPreserved s (blackBoxHook s) := by
    unfold blackBoxHook retHook
    simp only [vmPreserved_setPC, vmPreserved_writeReg64, vmPreserved_refl_iff]
  exact ⟨⟨hv.1.1, hv.1.2.1⟩, hv.2.1, hv.perm_eq, hv.fdsHiFrame⟩

private theorem vmNoTpidr_execInst {inst : Instr} (hnsvc0 : inst.isSvc0 = false) (s : State) :
    VmNoTpidr s (execInst inst s) := by
  have h := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s
  exact ⟨⟨h.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.1, fun a => congrFun h.2.1 a,
    LibsignalBinary.Heap.FdsHiFrame.of_fs_eq h.2.2.2.2.2.2⟩

private def bbTrapHooks : String → Option (State → State) :=
  fun n =>
    if n == lsBlackBoxU8Sym then some blackBoxHook
    else some (fun s => s.setStatus (.Exception "extern"))

private theorem findSome?_symbols_none {α : Type} :
    ∀ (syms : List (String × Nat)) {off : Nat},
      (syms.findSome? fun x => if x.2 == off then (none : Option α) else none) = none
  | [], _ => rfl
  | _ :: rest, _ => by
    rw [List.findSome?_cons, ite_self]
    exact findSome?_symbols_none rest

private theorem findSome?_bbTrapHooks_running {Hk : String → Option (State → State)}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State} {s : State},
      (l.findSome? fun (n, o) => if o == off then bbTrapHooks n else none) = some f →
      (f s).status = .Running →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = some blackBoxHook ∧
      f = blackBoxHook
  | [], _, _, _, h, _ => by simp at h
  | (n, o) :: tl, off, f, s, h, hrun => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : (n == lsBlackBoxU8Sym) = true
      · have hbb_eq : bbTrapHooks n = some blackBoxHook := by simp [bbTrapHooks, hn]
        rw [hbb_eq] at h
        injection h with hf
        subst hf
        have hn_eq : n = lsBlackBoxU8Sym := beq_iff_eq.mp hn
        subst hn_eq
        rw [h_bb]
        exact ⟨rfl, rfl⟩
      · simp only [Bool.not_eq_true] at hn
        have hbb_eq : bbTrapHooks n = some (fun s => s.setStatus (.Exception "extern")) := by
          simp [bbTrapHooks, hn]
        rw [hbb_eq] at h
        injection h with hf
        subst hf
        cases s
        cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_bbTrapHooks_running h_bb tl h hrun

private theorem findSome?_stubs_eq_none_of_bbTrapHooks (Hk : String → Option (State → State)) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then bbTrapHooks n else none) = none →
      (l.findSome? fun (n, o) => if o == off then Hk n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h
      by_cases hn : (n == lsBlackBoxU8Sym) = true <;> simp [bbTrapHooks, hn] at h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_eq_none_of_bbTrapHooks Hk tl h

private theorem externAt?_rebase_bbTrapHooks_running {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)} {f : State → State} {s : State}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    (hext : ((P.rebase b bbTrapHooks).withSvc noSyscalls).externAt? pc = some f)
    (hrun : (f s).status = .Running) :
    (P.rebase b Hk).externAt? pc = some blackBoxHook ∧ f = blackBoxHook := by
  unfold Program.withSvc at hext
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  cases hm : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then bbTrapHooks n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext
    injection hext with hgf
    subst hgf
    obtain ⟨hhk, hfg⟩ := findSome?_bbTrapHooks_running h_bb P.stubs hm hrun
    rw [hhk]
    exact ⟨rfl, hfg⟩

private theorem externAt?_rebase_eq_none_of_bbTrapHooks {P : Program} {b pc : BitVec 64}
    {Hk : String → Option (State → State)}
    (h : (P.rebase b bbTrapHooks).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at h ⊢
  dsimp only at h ⊢
  rw [findSome?_symbols_none] at h ⊢
  have h1 : (P.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then bbTrapHooks n else none) = none := by
    cases hm : (P.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then bbTrapHooks n else none) with
    | none => rfl
    | some g => rw [hm] at h; cases h
  rw [findSome?_stubs_eq_none_of_bbTrapHooks Hk P.stubs h1]
  rfl

private theorem steps_rebase_bbTrapHooks_noSyscalls {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
    {s sm : State}
    (hsteps : Steps ((P.rebase b bbTrapHooks).withSvc noSyscalls) s sm)
    (hrun_m : sm.status = .Running) :
    Steps (P.rebase b Hk) s sm ∧ VmNoTpidr s sm := by
  induction hsteps with
  | refl => exact ⟨Steps.refl _, VmNoTpidr.refl _⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hr2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_m
      | step hs _ => cases hs <;> assumption
    rcases ih hrun_m with ⟨hsteps_rest, hvm_rest⟩
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern_fault _ _ _ => cases s1; cases hr2
    | extern hr1 hext hkf hsym =>
      obtain ⟨hext_hk, rfl⟩ := externAt?_rebase_bbTrapHooks_running h_bb hext hr2
      exact ⟨Steps.step (Step.extern hr1 hext_hk hkf hsym) hsteps_rest,
        (vmNoTpidr_blackBoxHook s1).trans hvm_rest⟩
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
      have hev1 : ((P.rebase b bbTrapHooks).withSvc noSyscalls).evalInst inst s1 =
          execInst inst s1 :=
        Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
      have hev2 : (P.rebase b Hk).evalInst inst s1 = execInst inst s1 :=
        Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
      rw [hev1] at hsteps_rest hvm_rest
      exact ⟨Steps.step (hev2 ▸ Step.exec hr1 hfeH) hsteps_rest,
        (vmNoTpidr_execInst hnsvc0 s1).trans hvm_rest⟩

private theorem sepWP_rebase_bb_vmPreserved {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    (h_bb : Hk lsBlackBoxU8Sym = some blackBoxHook)
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
  · obtain ⟨hsteps_hk, hvm⟩ := steps_rebase_bbTrapHooks_noSyscalls h_bb hsteps hrun
    exact ⟨sm, hsteps_hk, Or.inl ⟨hpc, hrun, Pm, hPm, hvm.toVmPreserved htp, hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem sepWP_pull_vmPreserved_post {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {Pre R : SepProp} {Q : State → SepProp} {tail : State → Prop}
    (h : SepWP prog target_pc s0 Pre
      (fun sf P_f =>
        VmPreserved s0 sf ∧ ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf) ∧ tail sf))) :
    SepWP prog target_pc s0 Pre
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗ Q sf) ∧ tail sf) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hsat, htail⟩ =>
    ⟨fun hm => by rw [satisfies_pure_sepConj]; exact ⟨hvm, hsat hm⟩, htail⟩

local syntax "by_bb_vm_steps " term " => " tacticSeq : tactic

local elab_rules : tactic
  | `(tactic| by_bb_vm_steps $hbb:term => $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| apply sepWP_rebase_bb_vmPreserved $hbb))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``ProofLib.SepWP && ty.getAppNumArgs == 6 do
        throwError "by_bb_vm_steps: expected `SepWP`, got{Lean.indentExpr ty}"
      let e2 := ty.getArg! 0
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_bb_vm_steps: expected `Program.withSvc`, got{Lean.indentExpr e2}"
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn
        #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
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
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

section CtEqPlacedVm

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp] byte_bne_zext32 ite_bne_byte_0_1 setWidth32_ite_1_0 setWidth8_ite_1_0
  setWidth64_ite_1_0_32 setWidth64_ite_1_0_8 and64_ite_1_0 and64_1_ite_1_0 and64_mask32_ite_1_0
  and32_ite_1_0 and32_1_ite_1_0 Bool.and_assoc

@[local simp, local wp_norm, local arm64_norm]
private theorem tpidrEl0_blackBoxHook (s : State) : (blackBoxHook s).tpidrEl0 = s.tpidrEl0 := by
  unfold blackBoxHook retHook
  rfl

set_option maxHeartbeats 1600000 in
/-- Relocatable `[LibsignalPlacement]` contract with `VmPreserved` for
`<[u8] as ConstantTimeEq>::ct_eq` (Block `213`, `Keys.DefsBudget.ctEqSliceROSpec`). -/
theorem ct_eq_ro_placed_vm_ok [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec := by
  simp only [LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget.ctEqSliceROSpec,
    withVmPreserved, ctEqSliceROSpec]
  have hext :
      ((blkPC_213).rebase (blkPl_213).base bbTrapHooks).externAt? (lsρ lsBlackBoxU8Sym) =
        some blackBoxHook :=
    (ls_externAt?_of_mem).trans rfl
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
    pointsToBytesRO_eq_pointsToBytesRO32 (s0.readReg64 (Reg.gpr 1#5)) h]
  unfold pointsToBytes32 pointsToBytesRO32
  simp only [sepConj_assoc]
  apply sepWP_pull_vmPreserved_post
  by_bb_vm_steps h_bb =>
    iterate 33 (wp_steps; wp_black_box hext)
    rw [ct_eq_bool_32 h_4 h]
    wp_done

end CtEqPlacedVm

/-! ## 2. Relocatable `expand_multi_info` (Block `53`) with `VmPreserved` -/

private def kdfOnlyHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private instance instHkdfPlacedHooks_kdfOnly (C : Crypto) {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] : HkdfPlacedHooks C.F (kdfOnlyHooks H) where
  memset := by simp [kdfOnlyHooks, hH.memset]
  memcpy := by simp [kdfOnlyHooks, hH.memcpy]
  compress256 := by simp [kdfOnlyHooks, hH.compress256]

private theorem blk53_safeVm : checkBlockSafeVm blkLib_53.text = true := by decide +kernel
private theorem blk123_safeVm : checkBlockSafeVm blkLib_123.text = true := by decide +kernel

private noncomputable def keepExp [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a

private def ExpCodeLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  ∀ (H : LibsignalHooks),
    ((blkPC_53).rebase (blkPl_53).base H).CodeLoaded m ∧
    ((blkPC_123).rebase (blkPl_123).base H).CodeLoaded m

private theorem ExpCodeLoaded.of_keepsFrozenNoAnon [LibsignalPlacement] {m m' : Memory}
    (hcl : ExpCodeLoaded m) (hk : KeepsFrozenNoAnon m m') : ExpCodeLoaded m' :=
  fun H =>
    let ⟨h1, h2⟩ := hcl H
    ⟨CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h1 hk,
     CryptoVerification.LibsignalTripleRatchet.Expand.Program.CodeLoaded.of_keepsFrozenNoAnon h2 hk⟩

private theorem strip_codeLoaded_of_keep_sub {R : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hsub : ∀ a, ProofLib.progKeep R a = true → keep a = true)
    (hL : R.CodeLoaded m) : R.CodeLoaded (ProofLib.stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub_add : R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : keep (R.base + BitVec.ofNat 64 i) = true := by
    apply hsub
    unfold ProofLib.progKeep
    rw [hsub_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem expCodeLoaded_of_ls [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) : ExpCodeLoaded m := by
  intro H
  have hI53 : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base H) 53 H := inferInstance
  have hI123 : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  exact ⟨hI53.eq_blockProgram ▸ hcl 53 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI123.eq_blockProgram ▸ hcl 123 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

private theorem expCodeLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    ExpCodeLoaded (ProofLib.stripExecOutside keepExp m) := by
  intro H
  have hI53 : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base H) 53 H := inferInstance
  have hI123 : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  have hL53 : ((blkPC_53).rebase (blkPl_53).base H).CodeLoaded m :=
    hI53.eq_blockProgram ▸ hcl 53 (by decide) (by decide) H (fun _ => none) Syscall.standard
  have hL123 : ((blkPC_123).rebase (blkPl_123).base H).CodeLoaded m :=
    hI123.eq_blockProgram ▸ hcl 123 (by decide) (by decide) H (fun _ => none) Syscall.standard
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL53,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL123⟩
  · have ha' : ProofLib.progKeep ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) a = true := ha
    simp [keepExp, ha']
  · have ha' : ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a = true := ha
    simp [keepExp, ha']

private theorem runsTo_of_exp_123 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : ExpCodeLoaded s.mem)
    (h : RunsTo ((blkPC_123).rebase (blkPl_123).base H) s P_post) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base H) 53 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2
  have hext : ∀ pc, ((blkPC_123).rebase (blkPl_123).base H).externAt? pc =
      ((blkPC_53).rebase (blkPl_53).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_123).rebase (blkPl_123).base H).svc =
      ((blkPC_53).rebase (blkPl_53).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem expand_multi_info_exp_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : Nat} {s₀ : State}
    (hcl : ExpCodeLoaded s₀.mem)
    (hpre : ExpandPre expPlacedFakeB C.F prk info infoPtr okmLen s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info okmLen s₀) := by
  refine expand_multi_info_placed_runsTo_of_fin (fun hf hfin_pre => ?_) hpre
  have hcl_s : ExpCodeLoaded _ := hcl.of_keepsFrozenNoAnon (ExpandFrame.keepsFrozen hpre hf)
  exact runsTo_of_exp_123 hcl_s (finalize_fixed_placed_runsTo (H := H) hfin_pre)

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ∀ n, (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by
    simp [Memory.readBytes, ProofLib.strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, ProofLib.strip_read8]

private theorem strip_read64 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read64 a = m.read64 a := by
  simp [Memory.read64, ProofLib.strip_read8]

private theorem strip_readShaState (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside keep m) a = readShaState m a := by
  unfold readShaState
  congr 1; funext i
  exact strip_read32 keep m _

private theorem strip_writeBytes_comm (keep : BitVec 64 → Bool) :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (ProofLib.stripExecOutside keep m).writeBytes a bs =
        ProofLib.stripExecOutside keep (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes]
    rw [ProofLib.strip_write8, strip_writeBytes_comm keep bs (m.write8 a b) (a + 1#64)]

private theorem strip_permNoLazy_rw {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.permNoLazy a = some Perm.rw) :
    (ProofLib.stripExecOutside keep m).permNoLazy a = some Perm.rw := by
  dsimp only [ProofLib.stripExecOutside, Memory.permNoLazy] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc, Perm.rw] at h ⊢
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; cases keep a <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem hook_writeBytes_strip_vm (keep : BitVec 64 → Bool) (s : State)
    (bs : List (BitVec 8)) :
    returnToLinkRegister ((ProofLib.stripS keep s).setMem
        ((ProofLib.stripS keep s).mem.writeBytes ((ProofLib.stripS keep s).readReg64 .x0) bs)) =
      ProofLib.stripS keep
        (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) ∧
    VmPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) := by
  refine ⟨?_, ?_⟩
  · cases s
    dsimp only [ProofLib.stripS, returnToLinkRegister, State.setMem, State.setPC, State.readReg64]
    rw [strip_writeBytes_comm]
  · unfold returnToLinkRegister
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem kdfOnlyHooks_findSome?_active [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = some f →
      ∀ s : State,
        (f (ProofLib.stripS keepExp s)).status = .Running →
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f ∧
        f (ProofLib.stripS keepExp s) = ProofLib.stripS keepExp (f s) ∧
        VmPreserved s (f s)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : (n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym) = true
      · have hk_eq : kdfOnlyHooks H n = H n := by simp [kdfOnlyHooks, hn]
        rw [hk_eq] at h
        intro s _hrun
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with (rfl | rfl) | rfl
        · rw [hH.memset] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memsetHook
          simp only [stripS_readReg64]
          exact hook_writeBytes_strip_vm keepExp s _
        · rw [hH.memcpy] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memcpyHook
          simp only [stripS_readReg64]
          have hrd : (ProofLib.stripS keepExp s).mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
              s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat := by
            cases s; exact strip_readBytes keepExp _ _ _
          rw [hrd]
          exact hook_writeBytes_strip_vm keepExp s _
        · rw [hH.compress256] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold compress256Hook
          dsimp only []
          simp only [stripS_readReg64]
          have hst : readShaState (ProofLib.stripS keepExp s).mem (s.readReg64 .x0) =
              readShaState s.mem (s.readReg64 .x0) := by
            cases s; exact strip_readShaState keepExp _ _
          have hbs : (ProofLib.stripS keepExp s).mem.readBytes (s.readReg64 .x1)
                (64 * (s.readReg64 .x2).toNat) =
              s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat) := by
            cases s; exact strip_readBytes keepExp _ _ _
          rw [hst, hbs]
          exact hook_writeBytes_strip_vm keepExp s _
      · simp only [Bool.not_eq_true] at hn
        cases hHn : H n with
        | none =>
          have hk_n : kdfOnlyHooks H n = none := by unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact kdfOnlyHooks_findSome?_active (C := C) tl h
        | some g =>
          have hk_g : kdfOnlyHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_active (C := C) tl h

private theorem kdfOnlyHooks_findSome?_none {H : LibsignalHooks} :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hHn : H n with
      | none =>
        have hk : kdfOnlyHooks H n = none := by
          unfold kdfOnlyHooks; split <;> simp [hHn]
        rw [hk] at h
        exact kdfOnlyHooks_findSome?_none tl h
      | some g =>
        have hk : ∃ g', kdfOnlyHooks H n = some g' := by
          unfold kdfOnlyHooks
          split
          · exact ⟨g, hHn⟩
          · exact ⟨_, by rw [hHn]; rfl⟩
        rcases hk with ⟨g', hg'⟩
        rw [hg'] at h
        cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_none tl h

private theorem kdfOnlyHooks_externAt?_active [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {pc : BitVec 64} {f : State → State}
    (hext : ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keepExp s)).status = .Running) :
    ((blkPC_53).rebase (blkPl_53).base H).externAt? pc = some f ∧
    f (ProofLib.stripS keepExp s) = ProofLib.stripS keepExp (f s) ∧
    VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  cases hm : ((blkPC_53).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_53).base).toNat then kdfOnlyHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hvm⟩ :=
      kdfOnlyHooks_findSome?_active (C := C) (blkPC_53).stubs hm s hrun
    rw [hhk]
    exact ⟨rfl, hcomm, hvm⟩

private theorem kdfOnlyHooks_externAt?_none [LibsignalPlacement] {H : LibsignalHooks}
    {pc : BitVec 64}
    (hext : ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).externAt? pc = none) :
    ((blkPC_53).rebase (blkPl_53).base H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  have h1 : ((blkPC_53).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_53).base).toNat then kdfOnlyHooks H n else none) = none := by
    cases hm : ((blkPC_53).stubs.findSome? fun (n, o) =>
        if o == (pc - (blkPl_53).base).toNat then kdfOnlyHooks H n else none) with
    | none => rfl
    | some g => rw [hm] at hext; cases hext
  rw [kdfOnlyHooks_findSome?_none (blkPC_53).stubs h1]
  rfl

private theorem safeVm_of_block_progKeep
    (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (hchk : checkBlockSafeVm lib.text = true)
    {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hL : ((lib.program pl).rebase pl.base vmTrapHooks).CodeLoaded m)
    (hkeep : ProofLib.progKeep ((lib.program pl).rebase pl.base vmTrapHooks) pc = true)
    (hal_pc : pc.toNat % 4 = 0)
    (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall : Q.allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true :=
    placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) hchk
  have hLQ : Q.CodeLoaded m := hL.of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by
    have hcode : Q.code = lib.text.patched pl := rfl
    rw [hcode, Obj.CodeBlock.length_patched]
    omega
  have hoff_lt : (pc - Q.base).toNat < Q.code.length := by
    unfold ProofLib.progKeep at hkeep
    exact of_decide_eq_true hkeep
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned
  have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by
    conv_lhs => rw [hpc_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length := by omega
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by
      unfold Q Program.externAt? Program.hookAtOff? Program.rebase
      dsimp only
      rw [findSome?_symbols_none, findSome?_symbols_none]
      rfl
    have hce_Q : m.canExec pc 4 = true := by
      unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk
      have hk_lt : (pc - Q.base).toNat + k < Q.code.length := by omega
      have heq_addr : pc + BitVec.ofNat 64 k =
          Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) := by
        conv_lhs => rw [hpc_eq]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [heq_addr, hLQ.perm_eq _ hk_lt]
      rfl
    unfold Program.fetchMem
    rw [hext_Q]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
      not_true_eq_false, hce_Q, Bool.not_true]
    exact hdec
  have hboth := Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap
    (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hboth
  exact hboth

private theorem steps_exp_lockstep_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {s1 sf0 sf' : State}
    (hsteps0 : Steps ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)) s1 sf0)
    (hrun0 : sf0.status = .Running) :
    ∀ {s1' : State},
      s1' = ProofLib.stripS keepExp s1 →
      Steps ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)) s1' sf' →
      sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State,
        (sf = sf0 ∨ sf' = ProofLib.stripS keepExp sf) ∧
        Steps ((blkPC_53).rebase (blkPl_53).base H) s1 sf ∧
        VmPreserved s1 sf := by
  induction hsteps0 with
  | refl =>
    intro s1' _ _ _ _
    exact ⟨_, Or.inl rfl, .refl _, VmPreserved.refl _⟩
  | @step s1 s2 sf0 h1_0 hrest0 ih =>
    intro s1' hs1' hsteps' hrun_f hcl1
    cases hsteps' with
    | refl =>
      exact ⟨s1, Or.inr hs1', .refl s1, VmPreserved.refl s1⟩
    | @step _ s2' _ h1' hrest' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with
        | refl => exact hrun0
        | step hs _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with
        | refl => exact hrun_f
        | step hs _ => cases hs <;> assumption
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepExp s1).pc = s1.pc := by cases s1; rfl
          unfold Program.fetchMem at hfe'
          rw [hpc_eq, hext0] at hfe'
          simp at hfe'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepExp s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext0] at hext'
          injection hext' with hff'
          subst hff'
          obtain ⟨hext_H, hcomm, hvm1⟩ :=
            kdfOnlyHooks_externAt?_active (C := C) hext0 hr2'
          have hstep_H : Step ((blkPC_53).rebase (blkPl_53).base H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          have hcl2 : LibsignalCodeLoaded lsmpl (f s1).mem := hcl1.of_keepsFrozen hkf_s1
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hcomm hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := (blkPC_53).rebase (blkPl_53).base H
        have hext_kdf :
            ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).externAt? s1.pc = none := by
          cases he : ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).externAt? s1.pc with
          | none => rfl
          | some g => unfold Program.fetchMem at hfe0; rw [he] at hfe0; simp at hfe0
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keepExp s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext_kdf] at hext'; cases hext'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keepExp s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS keepExp s1).mem =
              ProofLib.stripExecOutside keepExp s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          have hext_H : P_H.externAt? s1.pc = none := kdfOnlyHooks_externAt?_none hext_kdf
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (ProofLib.stripExecOutside keepExp s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'
            rw [hext_kdf] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [strip_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
            have hxk := hce' k hk
            rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
          have hfe0' := hfe0
          unfold Program.fetchMem at hfe0'
          rw [hext_kdf] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem
            rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]
            exact hdec
          have hkeep_pc : keepExp s1.pc = true := by
            unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
            have hx0 := hce' 0 (by omega)
            simpa using (ProofLib.strip_perm_x_imp hx0).2
          have ⟨hnsvc0, hnmsr⟩ : inst'.isSvc0 = false ∧ inst'.isMsrTpidrEl0 = false := by
            unfold keepExp at hkeep_pc
            simp only [Bool.or_eq_true] at hkeep_pc
            rcases hkeep_pc with hk53 | hk123
            · have hI : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) 53 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_53).rebase (blkPl_53).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 53 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_53).rebase (blkPl_53).base vmTrapHooks =
                  (blkLib_53.program blkPl_53).rebase (blkPl_53).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_53).symm
              exact safeVm_of_block_progKeep blkLib_53 blkPl_53 blk53_safeVm
                (hEq ▸ hL) (hEq ▸ hk53) hal_pc hdec
            · have hI : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) 123 vmTrapHooks :=
                inferInstance
              have hL : ((blkPC_123).rebase (blkPl_123).base vmTrapHooks).CodeLoaded s1.mem :=
                hI.eq_blockProgram ▸ hcl1 123 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
              have hEq : (blkPC_123).rebase (blkPl_123).base vmTrapHooks =
                  (blkLib_123.program blkPl_123).rebase (blkPl_123).base vmTrapHooks :=
                hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_123).symm
              exact safeVm_of_block_progKeep blkLib_123 blkPl_123 blk123_safeVm
                (hEq ▸ hL) (hEq ▸ hk123) hal_pc hdec
          have hev0 : ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst' s1 =
              execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_kdf : ((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst'
              (ProofLib.stripS keepExp s1) =
              ProofLib.stripS keepExp
                (((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0, Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
          have hstep_H : Step P_H s1
              (((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            have := Step.exec (prog := P_H) hr1 hfe_H
            rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
          have hcl2 : LibsignalCodeLoaded lsmpl
              (((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst' s1).mem :=
            hcl1.of_keepsFrozen hstep_H.keepsFrozen
          have hvm1 : VmPreserved s1
              (((blkPC_53).rebase (blkPl_53).base (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            exact (vmNoTpidr_execInst hnsvc0 s1).toVmPreserved
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hev_kdf hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩

private theorem extract_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R) :
    LibsignalCodeLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsCodeLoaded] at hpre
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by sep_ac_rfl
  rwa [hcomm, satisfies_pure_sepConj] at hpre

/-- Relocatable `subroutine_ok` with `VmPreserved` for
`GenericHkdf<Hmac<Sha256>>::expand_multi_info` (Block `53`, `64` B and `80` B). -/
theorem expand_multi_info_placed_vm_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
      (withLsCodeLoaded lsmpl (withVmPreserved (expandMultiInfoSpec C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [withVmPreserved, expandMultiInfoSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA x.okmLen ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) (BitVec.ofNat 64 x.info.length)
  have hb_hdr : IsBlock
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = BitVec.ofNat 64 x.info.length) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA x.okmLen ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hokm_pos : 0 < x.okmLen := by omega
  have hrw_hm : s0.mem.RW x.hkdfA 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha
  have hrw_hdr : s0.mem.RW x.infoHdrA 16 := fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (s0.sp - 640#64) 640 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  let s0' := ProofLib.stripS keepExp s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExp s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha
    rw [hs0'_mem]
    exact strip_permNoLazy_rw (hrw a ha)
  have h_exp_pre0 : ExpandPre expPlacedFakeB C.F x.prk x.info x.infoA x.okmLen s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable hrw_hm
      read_x1 := by rw [hx1]; exact Memory.RW.readable hrw_hdr
      rw_x2 := by rw [hx2]; exact hrw_okm
      rw_stack := hrw_stk
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) hokm_pos hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) hokm_pos hsep_hdr_okm
      out_info_stk := ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have h_exp_pre' : ExpandPre expPlacedFakeB C.F x.prk x.info x.infoA x.okmLen s0' :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; simpa [s0', stripS_pc] using hpc
      status := by simpa [s0', stripS_status] using hrun
      x3_eq := by simpa [s0', stripS_readReg64] using hx3
      prk_le := hprk_le
      info_lt := hinfo_lt
      okm_len := hokm_len
      hmac_st := by
        rcases h_exp_pre0.hmac_st with ⟨h1, h2, h3, h4a, h4b, h4c, h4d⟩
        simp only [s0', stripS_readReg64, hs0'_mem]
        exact ⟨h1, by rwa [strip_readBytes], by rwa [ProofLib.strip_read8],
          by rwa [strip_readBytes], by rwa [strip_read64],
          by rwa [strip_readBytes], by rwa [strip_read64]⟩
      info_ptr := by
        simp only [s0', stripS_readReg64, hs0'_mem, strip_read64, hx1]
        exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by
        simp only [s0', stripS_readReg64, hs0'_mem, strip_read64, hx1]
        exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := by rw [hs0'_mem, strip_readBytes]; exact hro_info.read hsep_info_stk
      read_x0 := by
        simp only [s0', stripS_readReg64, hx0]
        exact Memory.RW.readable (hrw_strip hrw_hm)
      read_x1 := by
        simp only [s0', stripS_readReg64, hx1]
        exact Memory.RW.readable (hrw_strip hrw_hdr)
      rw_x2 := by simp only [s0', stripS_readReg64, hx2]; exact hrw_strip hrw_okm
      rw_stack := by simp only [s0', stripS_sp]; exact hrw_strip hrw_stk
      disj_x2_stack := by
        simp only [s0', stripS_readReg64, stripS_sp]
        exact h_exp_pre0.disj_x2_stack
      disj_x0_stack := by
        simp only [s0', stripS_readReg64, stripS_sp]
        exact h_exp_pre0.disj_x0_stack
      disj_x0_x2 := by
        simp only [s0', stripS_readReg64]
        exact h_exp_pre0.disj_x0_x2
      disj_x1_stack := by
        simp only [s0', stripS_readReg64, stripS_sp]
        exact h_exp_pre0.disj_x1_stack
      disj_x1_x2 := by
        simp only [s0', stripS_readReg64]
        exact h_exp_pre0.disj_x1_x2
      out_info_stk := by simp only [s0', stripS_sp]; exact h_exp_pre0.out_info_stk
      out_info_x2 := by simp only [s0', stripS_readReg64]; exact h_exp_pre0.out_info_x2
      sp_aligned := by simpa [State.spAligned, s0', stripS_sp] using hsp }
  let H' := kdfOnlyHooks H
  have hRuns0 := expand_multi_info_exp_runsTo (C := C) (H := H') (expCodeLoaded_of_ls hcl) h_exp_pre0
  have hRuns' := expand_multi_info_exp_runsTo (C := C) (H := H')
    (hs0'_mem ▸ expCodeLoaded_strip hcl) h_exp_pre'
  intro hL0
  have hL0_exp : ((blkPC_53).rebase (blkPl_53).base H').CodeLoaded s0.mem :=
    (expCodeLoaded_of_ls hcl) H' |>.1
  have hL0' : ((blkPC_53).rebase (blkPl_53).base H').CodeLoaded s0'.mem :=
    (hs0'_mem ▸ expCodeLoaded_strip hcl) H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL0_exp
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns' hL0'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_exp_lockstep_vm (C := C) (H := H) hsteps0 hpost0.2.1 rfl hsteps' hpost'.2.1 hcl
  have ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩ :
      TraceEq s0 sf ∧ ExpandPost C.F x.prk x.info x.okmLen s0 sf := by
    rcases hor with rfl | hsf_eq
    · exact ⟨htr0, hpost0⟩
    · subst hsf_eq
      rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hokm_sf', hframe_sf'⟩
      have hpc_sf : sf.pc = s0.readReg64 .x30 := by
        simpa [s0', stripS_pc, stripS_readReg64] using hpc_sf'
      have hstat_sf : sf.status = .Running := by
        simpa [stripS_status] using hstat_sf'
      have hcallee : CalleeSaved s0 sf := by
        refine ⟨by simpa [s0', stripS_sp] using hcallee'.1, fun r hr => ?_⟩
        simpa [s0', stripS_readReg64] using hcallee'.2 r hr
      have htr : TraceEq s0 sf :=
        ⟨by simpa [s0', stripS_trace] using htr'.1,
         by simpa [s0', stripS_calleeSavedVRegs] using htr'.2⟩
      have hsf_mem : (ProofLib.stripS keepExp sf).mem =
          ProofLib.stripExecOutside keepExp sf.mem := by
        cases sf; rfl
      have hx2_s0' : s0'.readReg64 .x2 = s0.readReg64 .x2 :=
        stripS_readReg64 keepExp s0 .x2
      have hsp_s0' : s0'.sp = s0.sp := stripS_sp keepExp s0
      have hokm_sf : sf.mem.readBytes (s0.readReg64 .x2) x.okmLen =
          hkdfExpand C.F x.prk x.info x.okmLen := by
        rw [← hx2_s0']
        rwa [hsf_mem, strip_readBytes] at hokm_sf'
      have hframe_sf : ExpandFrame x.okmLen s0 sf.mem := by
        unfold ExpandFrame Frame at hframe_sf' ⊢
        rcases hframe_sf' with ⟨hfr1, _hfr2, hfr3, hfr4, hfr5⟩
        refine ⟨?_, funext hvm.perm_eq, ?_, ?_, ?_⟩
        · intro a hout
          have h1 := hfr1 a (by rwa [hx2_s0', hsp_s0'])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_read8, ProofLib.strip_read8] at h1
        · intro a hout
          have h3 := hfr3 a (by rwa [hx2_s0', hsp_s0'])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree] at h3
        · intro a hlf
          have h4 := hfr4 a (by rwa [hs0'_mem, ProofLib.strip_isLazyFree])
          rwa [hsf_mem, ProofLib.strip_isLazyFree] at h4
        · intro a han
          have h5 := hfr5 a (by rwa [hs0'_mem, ProofLib.strip_isAnon])
          rwa [hsf_mem, ProofLib.strip_isAnon] at h5
      exact ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h80, hkdfExpand_80_eq]; simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info x.okmLen) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAux
