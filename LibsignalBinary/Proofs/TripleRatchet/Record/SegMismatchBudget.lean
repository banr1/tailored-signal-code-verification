/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
public meta import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Version-Mismatch Segment (`SegMismatchBudget`)

Relocatable `RustCliAllocBudget` / `SeamBudget` verification of `SegMismatch` (`+0x7e4 → +0x850`,
block 197), together with `A.atState ↦ A.repAlloc` representation normalizers and budget-aware call
tactics shared with `SegDecryptBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto ChainKey SessionState SignalMessage SignalProtocolError SenderChain
  InvalidMessageReason
)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecAt)
open CryptoVerification.LibsignalSessionRepr (
  VecPin ChainGhost vecGhostAt messageKeyAt optChainKeyAt chainAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SignalMessageGhost SenderChainGhost TailVecGhost SessionGhost
  UuidParser uuidTryParse
  optBoxU8At protocolAddressAt signalMessageAt optSenderChainAt optTailVecAt
  sessionStateAt invalidMessageStrAt speAt vecResultAt tapeAfter
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost recordResultAt
  sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  logClosurePlacedSpec logClosureSpec
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  RecErr recErrAt errsAt
  blkPC_197 blkPl_197 blkLib_197 blkLib_eq_197
  LibsignalCodeRoLoaded recFPCPlaced recExitPlaced recFramePlaced
  regionOutcome
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (
  draws_of_version_ne model_of_version_ne tapeAfter_zero mkTryDecryptGhost
  words6At memRegion48_eq_words6At
  stackAt_root_split_closure memRegion_5f0_split48 memRegion_192_split48
  errsAt_nil_unfold closureStack_to_growStack growStack_to_rootStack
  mismatch_errsAt_entails words6_5f0_to_memRegion sessionStateAt_exists_intro
  noPanic_onPanic_entails segDecrypt_replace_pre
  segDecrypt_of_sepWP_placed segDecrypt_of_sepWP_ret_placed segDecrypt_call_placed
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FitsEnv SeqEnv
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  TryDecryptEnvArgs FromFEnv
  tryDecryptPlacedSpec recordDecryptPlacedSpec
  MStatePlaced FStatePlaced SegMismatchPlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `A.atState lim st s ↦ A.repAlloc` representation normalizers -/

theorem live_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    (A.atState lim st s).live = A.repAlloc.live :=
  rfl

theorem live_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) :
    A.live = A.repAlloc.live :=
  rfl

theorem vecU8_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecU8 (A.atState lim st s) = vecU8 A.repAlloc :=
  rfl

theorem vecGhostAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecGhostAt (A.atState lim st s) = vecGhostAt A.repAlloc :=
  rfl

theorem vecAt_messageKey_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sz al : Nat) :
    vecAt (A.atState lim st s) sz al (messageKeyAt (A.atState lim st s)) =
      vecAt A.repAlloc sz al (messageKeyAt A.repAlloc) :=
  rfl

theorem optBoxU8At_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a ptr : BitVec 64) (o : Option (List (BitVec 8))) :
    optBoxU8At (A.atState lim st s) a ptr o = optBoxU8At A.repAlloc a ptr o := by
  cases o <;> rfl

theorem optChainKeyAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (pin : VecPin) (o : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt (A.atState lim st s) pin o a = optChainKeyAt A.repAlloc pin o a := by
  cases o <;> rfl

theorem chainAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (gc : ChainGhost × CryptoGames.LibsignalSession.ReceiverChain) (a : BitVec 64) :
    chainAt (A.atState lim st s) gc a = chainAt A.repAlloc gc a := by
  unfold chainAt
  rw [optChainKeyAt_atState]
  rfl

theorem chainAt_atState_fn {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    chainAt (A.atState lim st s) = chainAt A.repAlloc := by
  funext gc a
  exact chainAt_atState A lim st s gc a

theorem optSenderChainAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (g : Option SenderChainGhost) (sc : Option SenderChain) :
    optSenderChainAt (A.atState lim st s) a g sc = optSenderChainAt A.repAlloc a g sc := by
  cases g <;> cases sc <;>
    simp only [optSenderChainAt, optChainKeyAt_atState, vecGhostAt_atState, vecAt_messageKey_atState]

theorem optTailVecAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (size : Nat) (a : BitVec 64) (g : Option TailVecGhost) :
    optTailVecAt (A.atState lim st s) size a g = optTailVecAt A.repAlloc size a g := by
  cases g <;> rfl

theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt (A.atState lim st s) g a = protocolAddressAt A.repAlloc g a :=
  rfl

theorem signalMessageAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt (A.atState lim st s) g a m = signalMessageAt A.repAlloc g a m := by
  unfold signalMessageAt
  rw [optBoxU8At_atState]
  rfl

theorem sessionStateAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ss : BitVec 64) (G : SessionGhost) (mst : SessionState (List (BitVec 8))) :
    sessionStateAt (A.atState lim st s) ss G mst = sessionStateAt A.repAlloc ss G mst := by
  unfold sessionStateAt
  rw [chainAt_atState_fn, optSenderChainAt_atState, optTailVecAt_atState, optTailVecAt_atState]
  rfl

theorem invalidMessageStrAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (r : InvalidMessageReason) :
    invalidMessageStrAt (A.atState lim st s) a r = invalidMessageStrAt A.repAlloc a r := by
  cases r <;> rfl

theorem speAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (fnName : List (BitVec 8)) (a : BitVec 64) (e : SignalProtocolError) :
    speAt (A.atState lim st s) fnName a e = speAt A.repAlloc fnName a e := by
  cases e <;> simp only [speAt, invalidMessageStrAt_atState, vecU8_atState]

theorem vecResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    vecResultAt (A.atState lim st s) r res = vecResultAt A.repAlloc r res := by
  cases res with
  | ok _ => rfl
  | error e => exact speAt_atState A lim st s _ _ e

theorem recordResultAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (r : BitVec 64) (res : Except SignalProtocolError (List (BitVec 8))) :
    recordResultAt (A.atState lim st s) r res = recordResultAt A.repAlloc r res := by
  cases res with
  | ok _ => rfl
  | error e =>
    cases e with
    | invalidMessage t rsn =>
      cases rsn <;>
        simp only [recordResultAt, vecResultAt, speAt, invalidMessageStrAt_atState, vecU8_atState]
    | _ =>
      unfold recordResultAt vecResultAt
      exact speAt_atState A lim st s _ _ _

theorem recErrAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (p : BitVec 64) (r : RecErr) :
    recErrAt (A.atState lim st s) p r = recErrAt A.repAlloc p r := by
  cases r with
  | spe e => exact speAt_atState A lim st s _ _ e
  | version _ => rfl
  | iscmk => rfl

theorem errsAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (h : BitVec 64) (errs : List RecErr) :
    errsAt (A.atState lim st s) h errs = errsAt A.repAlloc h errs := by
  match errs with
  | [] => rfl
  | [r] =>
    simp only [errsAt, recErrAt_atState, live_atState]
  | _ :: _ :: _ => rfl

theorem recFramePlaced_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (x : RecordDecryptGhost) (sp : BitVec 64) :
    recFramePlaced (A.atState lim st s) x sp =
      recFramePlaced A.repAlloc x sp ∗ A.pool lim st s := by
  unfold recFramePlaced
  rw [protocolAddressAt_atState, protocolAddressAt_atState, signalMessageAt_atState,
    RustCliAllocBudget.atState_pool, RustCliAllocBudget.repAlloc_pool, sepConj_emp]
  simp only [sepConj_assoc]

/-! ## Block 197 `noSvc0` certificate, pool-sync macro, and budget call tactic -/

theorem checkBlockNoSvc0_197 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_197.text = true := by
  decide +kernel

macro "wp_steps_sync_197 " mid:term : tactic =>
  `(tactic| (
    apply LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm
      (Q := (blkPC_197).rebase (blkPl_197).base
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException _))
      blkLib_eq_197 checkBlockNoSvc0_197 (mid := $mid)
    intro _m_strip
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    first
      | refine ProofLib.SepWP.transport_budgetPool
          (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
          (hnext := ?_)
      | refine ProofLib.SepWP.transport_atStatePool
          (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
          (hnext := ?_)
  ))

open Lean Elab Tactic in
elab "segDecrypt_wpp_call_b " hcall:term:max a:term:max hF:term:max hpan:term:max : tactic => do
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
    | throwError "segDecrypt_wpp_call_b: unexpected subgoals"
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
      tryDecryptPlacedSpec, CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
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
    if !decl.isImplementationDetail && decl.userName.toString.startsWith "hsp" then
      let id := mkIdent decl.userName
      evalTactic (← `(tactic| try rw [$id:ident] at _hmR' ⊢))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals [gPanic]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      mkTryDecryptGhost,
      sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
      recordDecryptPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, Spec.inImage]
    intro _
    exact $hpan
  )))
  setGoals [gErr]
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only [withLsCodeLoaded, withVmPreserved, logClosurePlacedSpec, logClosureSpec,
      growOneSpeSpec, setSessionStateSpec, dropSessionStructureLocal2Spec,
      tryDecryptPlacedSpec, CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
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
    tryDecryptPlacedSpec, CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
    mkTryDecryptGhost,
    sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, memcpySpec,
    Spec.inImage]))
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
    (hL : ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem)
    (hwp : SepWPp ((blkPC_197).rebase (blkPl_197).base H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        ∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv).onPanic
          (x, st_init) s0 sf ∗ R))) :
    ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
      ((∃ st', FStatePlaced C A lim ctl uuidTryParse S tdEnv x st_init st' R s0 s') ∨
        regionOutcome (recordDecryptPlacedSpec C A lim ctl uuidTryParse S tdEnv)
          recExitPlaced (x, st_init) R s0 s') := by
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hF⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hF hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr ⟨hpan, hqp hmf⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Budget-threaded `segMismatch_placed_ok` -/

/-- Relocatable budget-threaded `SegMismatch` contract (`+0x7e4 → +0x850`). -/
theorem segMismatch_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    SegMismatchPlacedSpec C A lim ctl uuidTryParse S tdEnv H := by
  intro hgrow hclosure x st_init st G₁ R s0 s hM hL
  rcases hM with ⟨hsb, hpc, ⟨hrun, hsp, hsp_align, hx29, htr, hF0, hvregs⟩, hne, hx9, hmem⟩
  change s.pc = (blkPl_197).base + 2020#64 at hpc
  have hsp0 : s0.sp = s.sp := hsp.symm
  clear hsp
  have hfit_grow : FitsEnv M lim st (GrowOneSpeEnv 0#64) := hsb.1.seq_left
  rw [hsp0, recFramePlaced_atState, sessionStateAt_atState, sessionStateAt_atState,
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
  apply segDecrypt_of_sepWP_placed hF0 (mid := lsmpl.base 159)
  wp_steps_sync_197 (lsmpl.base 159)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF1
  segDecrypt_wpp_call_b hclosure () hF1 noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_placed hF_sf (mid := lsmpl.base 42)
  segDecrypt_wp_extract_exists
  rename_i hcl
  refine SepWP.transport_budgetPool hcl.1 (hnext := ?_)
  refine segDecrypt_replace_pre (closureStack_to_growStack s.sp) (by sep_focus) ?_
  wp_steps_sync_197 (lsmpl.base 42)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF2
  segDecrypt_wpp_call_b hgrow ((s.sp + 0x5d8#64, 0#64, 8#64, []), st) hF2
    noPanic_onPanic_entails
  apply segDecrypt_of_sepWP_ret_placed hF_sf_1
  segDecrypt_wp_extract_exists
  rename_i evs_grow p' hgrow_post
  rw [memRegion_192_split48 p', memRegion48_eq_words6At p']
  unfold words6At
  segDecrypt_wp_extract_exists
  wp_steps_sync_197 recFPCPlaced
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
    (draws_of_version_ne C x hne ▸ tapeAfter_zero ctl x.cur x.rest) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hF3 hmf
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
  · rw [hsp0, recFramePlaced_atState, sessionStateAt_atState]
    conv_rhs =>
      simp only [sessionStateAt_atState, errsAt_atState]
    unfold recFramePlaced
    rw [RustCliAllocBudget.repAlloc_pool, sepConj_emp]
    exact Eq.mp (congrArg (SepProp.Satisfies · _) (by sep_ac_rfl)) hmf

end LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget
