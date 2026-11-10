/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlaced
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegMismatch`

Threads `RustCliAllocBudget M` and `SeamBudget` across `segMismatch_placed_ok` and
`segMismatch_full_placed_ok` (`+0x7e4 → +0x850`) on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel RecordDecryptGhost sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (logClosurePlacedSpec logClosureSpec)
open CryptoVerification.LibsignalTripleRatchet.Record (errsAt regionOutcome)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  draws_of_version_ne model_of_version_ne mkTryDecryptGhost
  words6At memRegion48_eq_words6At
  stackAt_root_split_closure memRegion_5f0_split48 memRegion_192_split48
  errsAt_nil_unfold closureStack_to_growStack growStack_to_rootStack
  mismatch_errsAt_entails words6_5f0_to_memRegion sessionStateAt_exists_intro
  noPanic_onPanic_entails segDecrypt_replace_pre
  segDecrypt_of_sepWP_placed segDecrypt_of_sepWP_ret_placed segDecrypt_call_placed
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAt_entails_cliTapeAfter_zero)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  recFPCPlaced recExitPlaced recFramePlaced
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FitsEnv SeqEnv
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  live_repAlloc protocolAddressAt_atState signalMessageAt_atState
  sessionStateAt_atState vecResultAt_atState errsAt_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  cliRecFramePlaced_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  tryDecryptPlacedSpec recordDecryptPlacedSpec
  MStatePlaced FStatePlaced SegMismatchPlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sepWP_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post :=
  SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ => hp hvm

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

theorem sepWP_cut_here {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs1, ⟨_, _, Pm, hPm, h2⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sf, hs2, hout⟩ := SepWP.to_reaches_pc h2 hPm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

open Lean Elab Tactic in
elab "cli_segDecrypt_wpp_call_b " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (segDecrypt_call_placed $hcall (x := $a) $hF)
    { try wp_norm_goal; try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try wp_norm_goal; try assumption; try rfl }
    { simp only [Reg.lr, wp_norm, arm64_norm]; rfl }
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "cli_segDecrypt_wpp_call_b: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_loaded := ($hF).1
    have _hF_ro := ($hF).2
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      Spec.inImage]
    try simp (config := { decide := true }) only [
      sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      vecResultAt_atState, RustCliAllocBudget.atState_pool,
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail &&
        decl.userName.eraseMacroScopes.toString.startsWith "hsp" then
      let t ← Lean.Elab.Term.exprToSyntax (Lean.mkFVar decl.fvarId)
      evalTactic (← `(tactic| try rw [$t:term] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      Spec.inImage]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [withLsCodeLoaded, withVmPreserved,
    logClosurePlacedSpec, logClosureSpec,
    growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
    tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
    mkTryDecryptGhost,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
    Spec.inImage]))
  let mut oldHspTerms : Array Term := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail &&
        decl.userName.eraseMacroScopes.toString.startsWith "hsp" then
      oldHspTerms := oldHspTerms.push (← Lean.Elab.Term.exprToSyntax (Lean.mkFVar decl.fvarId))
  wpNormAndSplitHyp hspId
  for oldT in oldHspTerms do
    evalTactic (← `(tactic| try rw [$oldT:term] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldT in oldHspTerms do
    evalTactic (← `(tactic| try rw [$oldT:term]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
        vecResultAt_atState, RustCliAllocBudget.atState_pool,
        withLsCodeLoaded, Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

theorem seg_of_sepWPp_F_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (_htarget : target = recFPCPlaced)
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_463).rebase (blkPl_463).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        ∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).onPanic
          (x, st_init) s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      ((∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 s') ∨
        regionOutcome (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)
          recExitPlaced (x, st_init) R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hF hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 800000 in
theorem segMismatch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    SegMismatchPlacedSpec C A lim ctl uuidTryParse S tdEnv H := by
  intro hgrow hclosure x st_init st G₁ R s0 s hM hL
  rcases hM with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_463).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_grow : FitsEnv M lim st (GrowOneSpeEnv 0#64) := hsb.1.seq_left
  rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp,
    stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A.repAlloc s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_F_placed rfl hmem hL
  apply segDecrypt_of_sepWP_placed hF0 (mid := lsmpl.base 462)
  wp_step
  wp_step
  by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hF1
    have hvm0 : VmPreserved s _ := VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hvm1
    refine SepWPp.transport_budgetPool hvm0 (hnext := ?_)
    cli_segDecrypt_wpp_call_b hclosure () hF1 noPanic_onPanic_entails
    apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 42)
    segDecrypt_wp_extract_exists
    rename_i hcl
    refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
    refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
    by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hF2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
      cli_segDecrypt_wpp_call_b hgrow ((s.sp + 0x5d8#64, 0#64, 8#64, []), st) hF2
        noPanic_onPanic_entails
      apply segDecrypt_of_sepWP_ret_placed hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      by_vm_open (
        wp_steps
        rw [hsp_sf, live_repAlloc A]
        refine segDecrypt_replace_pre
          (mismatch_errsAt_entails A.repAlloc s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hgrow_post.2.1)
          (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (words6_5f0_to_memRegion s.sp 9223372036854775814#64
            (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
            w2 w3 w4 w5) (by sep_focus) ?_
        refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (draws_of_version_ne C x hne ▸ cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest)
          (by sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3 hF3 hmf
        rw [← A.pool_transport lim (M.stepEvents evs_grow st) sf_1 _ hvm3] at hmf
        refine ⟨M.stepEvents evs_grow st,
          hsb.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
          by unfold recFPCPlaced; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
        · refine ⟨by wp_norm_lhs,
                  by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                  by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                  by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                  by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr],
                  hF3,
                  by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState]
          conv_rhs =>
            simp only [sessionStateAt_atState, errsAt_atState]
          unfold recFramePlaced
          rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
          exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )
    )
  )

open Lean Elab Tactic in
elab "cli_segDecrypt_wpp_call_lsfull_b " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_call_lsfull $hcall (x := $a) $hF)
    { try wp_norm_goal; try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try wp_norm_goal; try assumption; try rfl }
    { simp only [Reg.lr, wp_norm, arm64_norm]; rfl }
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "cli_segDecrypt_wpp_call_lsfull_b: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_frozen := $hF
    have _hF_full := ($hF).2
    have _hF_loaded := CryptoVerification.LibsignalCodeLoaded.of_codeLoaded ($hF).2
    have _hF_ro := ($hF).1
    have _hF_cro := CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen ($hF)
    have _hF_tr_cro : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded _ _ :=
      ⟨_hF_loaded, _hF_ro⟩
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      Spec.inImage]
    try simp (config := { decide := true }) only [
      sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
      vecResultAt_atState, RustCliAllocBudget.atState_pool,
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail &&
        decl.userName.eraseMacroScopes.toString.startsWith "hsp" then
      let t ← Lean.Elab.Term.exprToSyntax (Lean.mkFVar decl.fvarId)
      evalTactic (← `(tactic| try rw [$t:term] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
      withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      Spec.inImage]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
    withLsCodeLoaded, withVmPreserved,
    logClosurePlacedSpec, logClosureSpec,
    growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
    tryDecryptPlacedSpec, CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
    mkTryDecryptGhost,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
    Spec.inImage]))
  let mut oldHspTerms : Array Term := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail &&
        decl.userName.eraseMacroScopes.toString.startsWith "hsp" then
      oldHspTerms := oldHspTerms.push (← Lean.Elab.Term.exprToSyntax (Lean.mkFVar decl.fvarId))
  wpNormAndSplitHyp hspId
  for oldT in oldHspTerms do
    evalTactic (← `(tactic| try rw [$oldT:term] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldT in oldHspTerms do
    evalTactic (← `(tactic| try rw [$oldT:term]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        sessionStateAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
        vecResultAt_atState, RustCliAllocBudget.atState_pool,
        CryptoVerification.LibsignalTripleRatchet.withLsFrozen,
        withLsCodeLoaded, Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

set_option maxHeartbeats 800000 in
/-- `[LibsignalFullPlacement]` `withLsFrozen` variant of `segMismatch_placed_ok` discharging the
log-closure premise internally. -/
theorem segMismatch_full_placed_ok [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.SegMismatchFullPlacedSpec
      C A lim ctl uuidTryParse S tdEnv H := by
  intro hgrow x st_init st G₁ R s0 s hM hFroz hL
  have _ := CryptoVerification.CliRatchet.DecPlaced.instIsLsBlockProg_463 H
  have hclosure :=
    LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget.log_closure_coins_frozen_vm_placed_ok_of_block
      (callerProg := (blkPC_463).rebase (blkPl_463).base H)
  rcases hM with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, _hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_463).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_grow : FitsEnv M lim st (GrowOneSpeEnv 0#64) := hsb.1.seq_left
  rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
    errsAt_atState] at hmem
  unfold recFramePlaced at hmem
  rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp,
    stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A.repAlloc s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_F_placed rfl hmem hL
  apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hFroz (mid := lsmpl.base 462)
  wp_step
  wp_step
  by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hF1
    have hvm0 : VmPreserved s _ := VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hvm1
    refine SepWPp.transport_budgetPool hvm0 (hnext := ?_)
    cli_segDecrypt_wpp_call_lsfull_b hclosure () hF1 noPanic_onPanic_entails
    apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 42)
    segDecrypt_wp_extract_exists
    rename_i hcl
    refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
    refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
    by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hF2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_)
      cli_segDecrypt_wpp_call_lsfull_b hgrow ((s.sp + 0x5d8#64, 0#64, 8#64, []), st) hF2
        noPanic_onPanic_entails
      apply CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegDecryptFacts.segDecrypt_of_sepWP_ret_lsfull hF_sf_1
      segDecrypt_wp_extract_exists
      rename_i evs_grow p' hgrow_post
      rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
      unfold words6At
      segDecrypt_wp_extract_exists
      by_vm_open (
        wp_steps
        rw [hsp_sf, live_repAlloc A]
        refine segDecrypt_replace_pre
          (mismatch_errsAt_entails A.repAlloc s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hgrow_post.2.1)
          (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (words6_5f0_to_memRegion s.sp 9223372036854775814#64
            (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
            w2 w3 w4 w5) (by sep_focus) ?_
        refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (sessionStateAt_exists_intro A.repAlloc (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
        refine segDecrypt_replace_pre
          (draws_of_version_ne C x hne ▸ cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest)
          (by sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm3 hF3 hmf
        rw [← A.pool_transport lim (M.stepEvents evs_grow st) sf_1 _ hvm3] at hmf
        refine ⟨M.stepEvents evs_grow st,
          hsb.step (fun _ _ => SeqEnv.append) hgrow_post.1.2,
          by unfold recFPCPlaced; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
        · refine ⟨by wp_norm_lhs,
                  by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
                  by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
                  by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
                  by simp only [wp_norm, arm64_norm, hgrow_post.1.1, hcl.2, htr],
                  CryptoVerification.Cli.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded.of_libsignalFrozen hF3,
                  by simp only [wp_norm, arm64_norm, *]⟩
        · rw [hsp0, cliRecFramePlaced_atState, sessionStateAt_atState]
          conv_rhs =>
            simp only [sessionStateAt_atState, errsAt_atState]
          unfold recFramePlaced
          rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
          exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf
      )
    )
  )

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
