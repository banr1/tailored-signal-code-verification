/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable CLI `SegMismatch` (`segMismatch_placed_ok`)

Proves the `[LibsignalPlacement]` and `[LibsignalFullPlacement]` version-mismatch error-push segment
(`+0x7e4 → +0x850`) on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.Record

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record hiding LibsignalCodeRoLoaded ls_externAt?_226 ls_hook_ok_226 recEntryPlaced recVPCPlaced recMPCPlaced recFPCPlaced recJPCPlaced recExitPlaced recMetaPlaced recFramePlaced tryDecryptPlacedSpec recordDecryptPlacedSpec VStatePlaced MStatePlaced FStatePlaced JStatePlaced SegClonePlacedSpec SegDecryptPlacedSpec SegMismatchPlacedSpec SegTailPlacedSpec SegExitPlacedSpec rootStack_le_of_recordPlacedPre recordDecrypt_placed_region_ok_of_seams segMismatch_placed_ok
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts hiding seg_of_sepWPp_F_placed
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.Cli.CoinsTape

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace SegDecryptFacts

open Lean Elab Tactic in
elab "cli_segDecrypt_wpp_call_placed " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
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
    | throwError "cli_segDecrypt_wpp_call_placed: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_loaded := ($hF).1
    have _hF_ro := ($hF).2
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      let id := mkIdent decl.userName
      evalTactic (← `(tactic| try rw [$id:ident] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec, recordDecryptSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec, growOneSpeSpec,
      setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec,
    growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
    tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
    sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]))
  let mut oldHspIds : Array Ident := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      oldHspIds := oldHspIds.push (mkIdent decl.userName)
  wpNormAndSplitHyp hspId
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        withLsCodeLoaded, Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))

theorem seg_of_sepWPp_F_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {P : SepProp}
    (_htarget : target = recFPCPlaced)
    (hm : s.mem ⊨ P ∗ R)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_463).rebase (blkPl_463).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → FStatePlaced C A ctl uuidTryParse S x R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A ctl uuidTryParse S).onPanic x s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      (FStatePlaced C A ctl uuidTryParse S x R s0 s' ∨
        regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hF hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem segDecrypt_of_sepWP_lsfull {prog : Program} {pl : Obj.MultiPlacement} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LibsignalFrozen pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalFrozen pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (libsignalFrozen_of_keepsFrozen hF hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem segDecrypt_of_sepWP_ret_lsfull {prog : Program} {pl : Obj.MultiPlacement} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : LibsignalFrozen pl s.mem)
    (h : SepWP prog ret s P (fun sf P_f => LibsignalFrozen pl sf.mem → Q sf P_f)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨hoom, hfalse⟩⟩ := h.elim hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq (libsignalFrozen_of_keepsFrozen hF hsteps.keepsFrozen)⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hoom, hfalse⟩)⟩

theorem segDecrypt_call_lsfull {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : LibsignalFrozen pl s.mem)
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : (∀ code sf, spec.onExit x code s sf = ⌜False⌝) ∧
      (∀ sf, spec.onOom x s sf = ⌜False⌝))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → LibsignalFrozen pl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf' P_f => (sf'.mem ⊨ P_f ∗ R) → (sf'.mem ⊨ Qpan sf' ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (libsignalFrozen_of_keepsFrozen hF hsteps.keepsFrozen) R' hpost
        (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq.1] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · rw [hexit_eq.2] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

open Lean Elab Tactic in
elab "cli_segDecrypt_wpp_call_lsfull " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hFId ← freshIdent `hF_sf
  evalTactic (← `(tactic| (
    apply (segDecrypt_call_lsfull $hcall (x := $a) $hF)
    { try wp_norm_goal; try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try assumption; try rfl }
    { try wp_norm_lhs; try wp_norm_goal; try assumption; try rfl }
    { simp only [Reg.lr, wp_norm, arm64_norm]; rfl }
  )))
  let gsAfterSetup ← getGoals
  let gPre :: gPanic :: gErr :: gCont :: rest := gsAfterSetup
    | throwError "cli_segDecrypt_wpp_call_lsfull: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| (
    intro _R' _hmR'
    have _hF_frozen := $hF
    have _hF_full := ($hF).2
    have _hF_loaded := LibsignalCodeLoaded.of_codeLoaded ($hF).2
    have _hF_ro := ($hF).1
    have _hF_cro := LibsignalCodeRoLoaded.of_libsignalFrozen ($hF)
    have _hF_tr_cro : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded _ _ :=
      ⟨_hF_loaded, _hF_ro⟩
  )))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsFrozen, withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    try simp (config := { decide := true }) only [
      stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc,
      wp_norm, arm64_norm] at _hmR' ⊢
    repeat' (rcases _hmR' with ⟨_, _hmR'⟩)
  )))
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      let id := mkIdent decl.userName
      evalTactic (← `(tactic| try rw [$id:ident] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsFrozen, withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec, recordDecryptSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsFrozen, withLsCodeLoaded, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec, tryDecryptPlacedSpec,
      tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
      sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  )))
  setGoals (gCont :: rest)
  evalTactic (← `(tactic|
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hFId:ident
  ))
  foldStructEtaTarget
  evalTactic (← `(tactic| try dsimp only [withLsFrozen, withLsCodeLoaded, logClosurePlacedSpec,
    logClosureSpec, growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
    tryDecryptPlacedSpec, tryDecryptSpecQF', tryDecryptSpec, mkTryDecryptGhost,
    sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec, Spec.inImage]))
  let mut oldHspIds : Array Ident := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      oldHspIds := oldHspIds.push (mkIdent decl.userName)
  wpNormAndSplitHyp hspId
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident] at $hspId:ident))
  wpNormAndSplitHyp hcsId
  evalTactic (← `(tactic| try rw [$hspId:ident]))
  for oldId in oldHspIds do
    evalTactic (← `(tactic| try rw [$oldId:ident]))
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        withLsFrozen, withLsCodeLoaded, Spec.inImage,
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hspId:ident]))))


end SegDecryptFacts

open SegDecryptFacts

attribute [local irreducible] Program.fetch Program.externAt?

theorem segMismatch_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} :
    SegMismatchPlacedSpec C A ctl uuidTryParse S H := by
  intro hgrow hclosure x G₁ R s0 s hM hL
  rcases hM with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_463).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  unfold recFramePlaced at hmem
  rw [hsp0, stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_F_placed rfl hmem hL
  apply segDecrypt_of_sepWP_placed hF0 (mid := lsmpl.base 462)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  cli_segDecrypt_wpp_call_placed hclosure () hF1 noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 42)
  segDecrypt_wp_extract_exists
  rename_i htr_sf
  refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF2
  cli_segDecrypt_wpp_call_placed hgrow (s.sp + 0x5d8#64, 0#64, 8#64, []) hF2
    (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_sf, htr]))
  apply segDecrypt_of_sepWP_ret_placed hF_sf_1
  segDecrypt_wp_extract_exists
  rename_i p' hp'
  rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
  unfold words6At
  segDecrypt_wp_extract_exists
  wp_steps
  rw [hsp_sf]
  refine segDecrypt_replace_pre
    (mismatch_errsAt_entails A s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hp'.2) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (words6_5f0_to_memRegion s.sp 9223372036854775814#64
      (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
      w2 w3 w4 w5) (by sep_focus) ?_
  refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
  refine segDecrypt_replace_pre (sessionStateAt_exists_intro A (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (draws_of_version_ne C x hne ▸ cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3 hmf
  refine ⟨by unfold recFPCPlaced; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
  · refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
            by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
            by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
            by simp only [wp_norm, arm64_norm, hp'.1, htr_sf, htr],
            hF3,
            by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
  · unfold recFramePlaced
    rw [hsp0]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

theorem segMismatch_full_placed_ok [LibsignalFullPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    {x : RecordDecryptGhost} {G₁ : SessionGhost} {R : SepProp} {s0 s : State}
    (hM : MStatePlaced A ctl x G₁ R s0 s)
    (hFroz : LibsignalFrozen lsmpl s.mem)
    (hL : ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem) :
    ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
      (FStatePlaced C A ctl uuidTryParse S x R s0 s' ∨
        regionOutcome (recordDecryptPlacedSpec C A ctl uuidTryParse S) recExitPlaced x R s0 s') := by
  have hclosure :=
    log_closure_coins_frozen_placed_ok_of_block (callerProg := (blkPC_463).rebase (blkPl_463).base H)
  rcases hM with ⟨hpc, ⟨hrun, hsp, hsp_align, hx29, htr, _hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_463).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  unfold recFramePlaced at hmem
  rw [hsp0, stackAt_root_split_closure s.sp, memRegion_5f0_split48 s.sp,
    memRegion48_eq_words6At (s.sp + 0x5f0#64), errsAt_nil_unfold A s.sp] at hmem
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem
  rcases hmem with ⟨w0, w1, w2, w3, w4, w5, hmem⟩
  unfold words6At at hmem
  simp only [← sepConj_assoc] at hmem
  apply seg_of_sepWPp_F_placed rfl hmem hL
  apply segDecrypt_of_sepWP_lsfull hFroz (mid := lsmpl.base 462)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  cli_segDecrypt_wpp_call_lsfull hclosure () hF1 noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_lsfull hF_sf (mid := lsmpl.base 42)
  segDecrypt_wp_extract_exists
  rename_i htr_sf
  refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF2
  cli_segDecrypt_wpp_call_lsfull hgrow (s.sp + 0x5d8#64, 0#64, 8#64, []) hF2
    (grow_onPanic_entails (by simp only [wp_norm, arm64_norm, htr_sf, htr]))
  apply segDecrypt_of_sepWP_ret_lsfull hF_sf_1
  segDecrypt_wp_extract_exists
  rename_i p' hp'
  rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
  unfold words6At
  segDecrypt_wp_extract_exists
  wp_steps
  rw [hsp_sf]
  refine segDecrypt_replace_pre
    (mismatch_errsAt_entails A s.sp p' w1 w2 w3 w4 w5 x.msg.messageVersion hp'.2) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (words6_5f0_to_memRegion s.sp 9223372036854775814#64
      (w1 &&& 18446744069414584320#64 ||| BitVec.zeroExtend 64 x.msg.messageVersion)
      w2 w3 w4 w5) (by sep_focus) ?_
  refine segDecrypt_replace_pre (growStack_to_rootStack s.sp) (by sep_focus) ?_
  refine segDecrypt_replace_pre (sessionStateAt_exists_intro A (s.sp + 3232#64) G₁ x.st) (by sep_focus) ?_
  refine segDecrypt_replace_pre
    (draws_of_version_ne C x hne ▸ cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3 hmf
  refine ⟨by unfold recFPCPlaced; wp_norm_lhs, ?_, model_of_version_ne C S x hne, ?_⟩
  · refine ⟨by wp_norm_lhs,
            by simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf, hsp0],
            by unfold State.spAligned; simp only [wp_norm, arm64_norm, hsp_sf_1, hsp_sf]; exact hsp_align,
            by simp only [wp_norm, arm64_norm, hcs_sf_1, hcs_sf]; exact hx29,
            by simp only [wp_norm, arm64_norm, hp'.1, htr_sf, htr],
            LibsignalCodeRoLoaded.of_libsignalFrozen hF3,
            by simp only [wp_norm, arm64_norm, hvregs_2, hvregs_1, hvregs]⟩
  · unfold recFramePlaced
    rw [hsp0]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by ac_rfl)) hmf

end CryptoVerification.Cli.LibsignalTripleRatchet.Record
