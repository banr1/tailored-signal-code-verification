/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClosureStubs4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Seg7a4K
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-!
# Budget-Threaded 4K-Stack `set_session_state` & Post-`tryDecrypt` Closure Blocks

1. Verifies `<SessionRecord>::set_session_state` against `setSessionStateSpec M A lim` on
   `tripleRatchetProgAtExt b ext` under `AllocContractsMem4KBudget b M A lim ext`.
2. Proves `VmPreserved`-strengthened post-`tryDecrypt` closure basic-block steps
   (`p3_seg7a_x24_ext_4k_vm_wp`, `p3_seg7b_x24_ext_vm_wp`, `p3_err_dup_ext_vm_wp`,
   `p3_err_tail_dup_a_ext_vm_wp`, `p3_err_tail_b_ext_vm_wp`).
-/

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec setSessionStateSpec growOneSpeSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  adrp_closure_logMaxLevel_seg7a closureMemcpyRelOff
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget (
  AllocContractsMem4KBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget (
  dropSessionStructureLocal1SpecBase drop_session_structure_local1_ok_ext_4k
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] sessionMemcpyBudgetSpec sessionMemcpySpec libcMemcpySpec

private theorem sepWP_seg_rebase_vm {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → sm.pc = mid → sm.status = .Running →
          SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc (sepWP_rebase_vmPreserved hseg) hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (hcont hvm hpcm hrunm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem pool_sync {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    A.pool lim st s = A.pool lim st sm :=
  (A.pool_of_vmPreserved hvm).symm

private def freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s

private theorem freeOnlyPool_sync {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sm : State} (hvm : VmPreserved s sm) :
    freeOnlyPool A lim st s = freeOnlyPool A lim st sm := by
  dsimp only [freeOnlyPool]
  congr 1
  funext evs
  rw [pool_sync A lim (M.stepEvents evs st) hvm]

private theorem freeOnlyPool_step_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (s : State) :
    A.pool lim (M.stepEvents evs st) s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right evs (Entails.pure_right hevs (Entails.refl _))

private theorem sepWP_sync_and_fold_freeOnlyPool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    {prev s : State} (hvm : VmPreserved prev s) :
    A.pool lim (M.stepEvents evs st) prev ⊢ freeOnlyPool A lim st s := by
  rw [pool_sync A lim (M.stepEvents evs st) hvm]
  exact freeOnlyPool_step_here A lim st hevs s

private theorem fnAddr_tripleRatchet_eq_trapHooks (b : BitVec 64)
    (ext : String → Option (State → State)) (name : String) :
    (tripleRatchetProgAtExt b ext).fnAddr name =
      (libsignalSessionCode.rebase b trapHooks).fnAddr name := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]

attribute [local irreducible] freeOnlyPool

local elab "wp_steps_sync_pool " mid:term : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply sepWP_seg_rebase_vm (P := libsignalSessionCode) (mid := $mid)))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let outerLCtx ← Lean.getLCtx
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn
      #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| (
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by first | rfl | simp only [wp_norm, arm64_norm], ?_⟩)))
    let rem ← Lean.Elab.Tactic.getGoals
    let [remId] := rem
      | throwError "wp_steps_sync_pool: expected 1 continuation goal, got {rem.length}"
    let (newArgFVars, newNames, contForallType) ← remId.withContext do
      let remLCtx ← Lean.getLCtx
      let mut fvs : Array Lean.Expr := #[]
      let mut argFvs : Array Lean.Expr := #[]
      let mut nms : Array Lean.Name := #[]
      for decl in remLCtx do
        if !decl.isImplementationDetail && !outerLCtx.contains decl.fvarId then
          fvs := fvs.push decl.toExpr
          if !decl.isLet then
            argFvs := argFvs.push decl.toExpr
            nms := nms.push decl.userName
      let remType ← Lean.instantiateMVars (← remId.getType)
      let cTy ← Lean.Meta.mkForallFVars fvs remType (usedLetOnly := false)
      pure (argFvs, nms, cTy)
    let gNext ← Lean.Meta.mkFreshExprMVar contForallType
    Lean.Meta.withLocalDeclD `_fn_next contForallType fun fnNext => do
      remId.assign (Lean.mkAppN fnNext newArgFVars)
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2
        else if sub.eqv e1 then some e2
        else none
      let prfLam ← Lean.Meta.mkLambdaFVars #[fnNext] prf2
      g.assign (Lean.mkApp prfLam gNext)
    let mut gCur := gNext.mvarId!
    for nm in newNames do
      let (_, gCur') ← gCur.intro nm
      gCur := gCur'
    Lean.Elab.Tactic.setGoals (gCur :: savedGoals.tail!)
    let idHvm := Lean.mkIdent `_hvm
    let idHpcm := Lean.mkIdent `_hpcm
    let idHrunm := Lean.mkIdent `_hrunm
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| (
        intro $idHvm:ident $idHpcm:ident $idHrunm:ident
        try (conv => arg 4; simp only [pool_sync _ _ _ $idHvm:ident, freeOnlyPool_sync _ _ _ $idHvm:ident]))))

/-! ## Part 1: Budget-Threaded `<SessionRecord>::set_session_state` -/

private theorem stackAt_setSessionState_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp dropSessionStructureLocal1Stack 4 (by decide)
  change stackAt sp setSessionStateStack =
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]
  simp only [sepExists_sepConj_right]

private theorem stackAt_setSessionState_split_alloc_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [show setSessionStateStack = allocHookStack + 160 from rfl,
      stackAt_split_bottom' sp allocHookStack 160 (by decide)]

private theorem cells4_local1_entails_setSessionState_split_4k (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [← stackAt_setSessionState_split_alloc_4k sp, stackAt_setSessionState_4k sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem pointsTo64_memRegion_336_eq_344_4k (r : BitVec 64) :
    (∃∗ v : BitVec 64, ((r + 24#64) ↦₆₄ v)) ∗ memRegion (r + 32#64) 336 =
      memRegion (r + 24#64) 344 := by
  have h := memRegion_split (r + 24#64) 8 336 (by decide)
  have hadd : r + 24#64 + 8#64 = r + 32#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (8 + 336 : Nat) = 344 by rfl, hadd, ProofLib.memRegion_eight] at h
  exact h.symm

private theorem pointsTo64_memRegion_336_entails_344_4k (r v : BitVec 64) :
    ((r + 24#64) ↦₆₄ v) ∗ memRegion (r + 32#64) 336 ⊢ memRegion (r + 24#64) 344 := by
  rw [← pointsTo64_memRegion_336_eq_344_4k r]
  exact sepConj_mono_left (Entails.sepExists_intro v)

private theorem cap_add_one_beq_zero_eq_false_4k {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

private def vecGhostTailAt4K (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap_4k (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt4K A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt4K]
  ac_rfl

private def sessionStateAfterLocalIk4K (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap_4k (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt4K A G.localIk ss ∗
      sessionStateAfterLocalIk4K A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk4K
  rw [vecGhostAt_unfold_cap_4k]
  ac_rfl

private def dropSessionStructureLocal1HeadSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧
      x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt4K A.repAlloc x.G.localIk x.ss ∗
      sessionStateAfterLocalIk4K A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack

private theorem drop_session_structure_local1_head_ok_4k {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop1 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1HeadSpec4K M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  refine hdrop1.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [dropSessionStructureLocal1SpecBase, dropSessionStructureLocal1HeadSpec4K,
    sessionStateAt_unfold_cap_4k, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

private def setSessionStateNoneSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, bs), st) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      ((record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (record + 0x20#64) 336 ∗
      (src ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt s.sp setSessionStateStack
  post := fun ((record, src, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf ∗
      stackAt s0.sp setSessionStateStack

private theorem set_session_state_none_ok_4k {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpyBudgetSpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateNoneSpec4K M A lim) := by
  unfold setSessionStateNoneSpec4K
  simp only [noneCap]
  have hfn : libsignalSessionCode.fnOff setSessionStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      (sessionMemcpyBudgetSpec allocHookStack) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hmemcpy0 setSessionStateName
      (num% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
      (by fnoff_eq)
  clear hmemcpy0
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0x34 8
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr setSessionStateName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr setSessionStateName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext setSessionStateName
  rw [hfn_eq] at hmemcpy ⊢
  dsimp only [tripleRatchetProgAtExt] at hmemcpy ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr setSessionStateName = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨⟨record, src, bs⟩, st⟩ := x
  dsimp only at *
  have hbs_len : bs.length = 344 := by assumption
  rw [stackAt_setSessionState_split_alloc_4k s0.sp]
  wp_steps_sync_pool (entry + BitVec.ofNat 64 (num% (ls_off% "memcpy" -
    ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
  refine SepWP.fold (pointsTo64_memRegion_336_entails_344_4k record 0xffffffffffffffff#64)
    (by sep_focus) ?_
  rw [← hbs_len]
  wp_call hmemcpy (record + 24#64, src, bs)
  rw [pool_sync A lim st ‹VmPreserved _ sf›]
  rw [← stackAt_setSessionState_split_alloc_4k s0.sp]
  wp_done

private def setSessionStateSomeStack4K (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)

private def setSessionStateSomeSpec4K (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × SessionGhost ×
      SessionState (List (BitVec 8)) × List (BitVec 8)) × M.σ) where
  pre := fun ((record, src, G, sessSt, bs), st) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      sessionStateAt A.repAlloc (record + 0x18#64) G sessSt ∗
      (src ↦ₛ bs) ∗ A.pool lim st s ∗ setSessionStateSomeStack4K s.sp
  post := fun ((record, src, _G, _sessSt, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗
      freeOnlyPool A lim st sf ∗ stackAt s0.sp setSessionStateStack

private theorem set_session_state_some_ok_4k {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpyBudgetSpec allocHookStack))
    (hdrop1 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSomeSpec4K M A lim) := by
  unfold setSessionStateSomeSpec4K
  simp only [sessionStateAt_unfold_cap_4k, setSessionStateSomeStack4K, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff setSessionStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      (sessionMemcpyBudgetSpec allocHookStack) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hmemcpy0 setSessionStateName
      (num% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
      (by fnoff_eq)
  clear hmemcpy0
  have hdrop := drop_session_structure_local1_head_ok_4k hdrop1
  clear hdrop1
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name =
      (tripleRatchetProgAtExt b ext).fnAddr setSessionStateName +
        bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
          (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"),
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state"),
      BitVec.add_assoc]
    rfl
  rw [hrel] at hdrop
  clear hrel
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0 60
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr setSessionStateName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr setSessionStateName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext setSessionStateName
  rw [hfn_eq] at hmemcpy hdrop ⊢
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1HeadSpec4K] at hmemcpy hdrop ⊢
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr setSessionStateName = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨⟨record, src, G, sessSt, bs⟩, st⟩ := x
  dsimp only at *
  have hbs_len : bs.length = 344 := by assumption
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_4k (by omega)
  wp_steps_sync_pool (entry +
    bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") -
      (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
  wp_call hdrop (⟨record + 24#64, G, sessSt⟩, st)
  try wp_pull_exists
  repeat clear ‹VmPreserved _ _›
  wp_steps_sync_pool (entry + BitVec.ofNat 64 (num% (ls_off% "memcpy" -
    ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
  have hvm_box : True ∧ _ := ⟨trivial, ‹VmPreserved _ _›⟩
  repeat clear ‹VmPreserved _ _›
  refine SepWP.fold (cells4_local1_entails_setSessionState_split_4k s0.sp _ _ _ _)
    (by sep_focus) ?_
  rw [show memRegion (record + 24#64) 344 = memRegion (record + 24#64) bs.length by rw [hbs_len]]
  wp_call hmemcpy (record + 24#64, src, bs)
  have hvm_tot := hvm_box.2.trans ‹VmPreserved _ _›
  apply SepWP.fold (sepWP_sync_and_fold_freeOnlyPool A lim st ‹FreeOnlyEvs _› hvm_tot) (by sep_focus)
  refine SepWP.fold (Entails.of_eq (stackAt_setSessionState_split_alloc_4k s0.sp).symm)
    (by sep_focus) ?_
  wp_done

theorem set_session_state_ok_of_memcpy_4k {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpyBudgetSpec allocHookStack))
    (hdrop1 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSpec M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨⟨record, src, cur, bs⟩, st⟩ R s0 hpc hrun hpre hsp => ?_
  rcases cur with _ | ⟨G, sessSt⟩
  · refine (set_session_state_none_ok_4k hmemcpy0).mono_outcome ((record, src, bs), st) R s0
      hpc hrun (by simpa only [setSessionStateSpec, setSessionStateNoneSpec4K, sepConj_assoc] using hpre)
      hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [setSessionStateNoneSpec4K, setSessionStateSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨htr, hpost⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨[], ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr, FreeOnlyEvs.nil, fun _ => rfl⟩, ?_⟩
      simpa only [M.stepEvents_nil, sepConj_assoc] using hpost
    · exact (not_satisfies_false_sepConj hpan).elim
    · exact (not_satisfies_false_sepConj hex).elim
    · exact (not_satisfies_false_sepConj hoom).elim
  · refine (set_session_state_some_ok_4k hmemcpy0 hdrop1).mono_outcome
      ((record, src, G, sessSt, bs), st) R s0 hpc hrun
      (by simpa only [setSessionStateSpec, setSessionStateSomeSpec4K,
        stackAt_setSessionState_4k, setSessionStateSomeStack4K, sepConj_assoc] using hpre)
      hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [setSessionStateSomeSpec4K, setSessionStateSpec] at hpost ⊢
      unfold freeOnlyPool at hpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨htr, hpost⟩
      have hpost1 : sf.mem ⊨
          (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
          (((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp setSessionStateStack ∗ R) := by
        convert hpost using 1
        sep_ac_rfl
      rw [sepExists_sepConj_left, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨evs, hpost1⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hevs, hpost1⟩
      rw [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨evs, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr, hevs, fun h => by cases h⟩, ?_⟩
      convert hpost1 using 1
      sep_ac_rfl
    · exact (not_satisfies_false_sepConj hpan).elim
    · exact (not_satisfies_false_sepConj hex).elim
    · exact (not_satisfies_false_sepConj hoom).elim

theorem set_session_state_ok_ext_4k {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSpec M A lim) :=
  set_session_state_ok_of_memcpy_4k hA.session_memcpy (drop_session_structure_local1_ok_ext_4k hA)

theorem set_session_state_ok_ext {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSpec M A lim) :=
  set_session_state_ok_ext_4k (AllocContractsMem4KBudget.of_AllocContracts hA)

/-! ## Part 2: `VmPreserved`-Strengthened Post-`tryDecrypt` Closure Blocks -/

section ClosureVmBlocks

attribute [local irreducible] Program.fnOff

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "memcpy")

theorem p3_seg7a_x24_ext_4k_vm_wp {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4KBudget b M A lim ext)
    (s : State) (coroPtr retPtr : BitVec 64)
    (ssBytes : List (BitVec 8))
    (hb : b &&& 0xfff#64 = 0#64)
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗ stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1dfc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureMemcpyRelOff)
      (sessionMemcpyBudgetSpec allocHookStack) :=
    hA.session_memcpy_ok_at decryptPrekeyClosureName
      (num% ((2^64 + ls_off% "memcpy" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (by simp only [arm64_norm])
  closure_fetches_range_cli b trapHooks 0x1cd8 0x1cf8
  closure_fetches_range_cli b trapHooks 0x1de0 0x1df8
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext decryptPrekeyClosureName
  rw [hfn_eq] at hmemcpy hpc ⊢
  dsimp only [tripleRatchetProgAtExt] at hmemcpy ⊢
  have hentry : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_logMaxLevel_seg7a hb hentry).1
  have hadrp := (adrp_closure_logMaxLevel_seg7a hb hentry).2
  have htarget : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName +
      0x1df8#64 + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7672)) % 2^64) =
      b + (bv% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hlog :
      (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
        b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    bv_arith
  rw [← hss_len]
  wp_steps_sync_pool (entry + closureMemcpyRelOff)
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  have hvm_1 : VmPreserved s sf := _hvm.trans ‹VmPreserved _ sf›
  refine SepWP.mono (post := fun s1 P_f =>
    VmPreserved sf s1 ∧
    (P_f ⊢
      ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
      ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
      ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗ stackAt s.sp allocHookStack) ∧
    s1.sp = s.sp ∧
    s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
    s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
    s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
    s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
    s1.readReg64 .x29 = s.readReg64 .x29 ∧
    s1.readReg64 .x30 = entry + 0x1dfc#64 ∧
    calleeSavedVRegs s1 = calleeSavedVRegs s) ?_ (fun s1 P_f _ _ ⟨hvm2, hrest⟩ => ⟨hvm_1.trans hvm2, hrest⟩)
  by_vm_steps
    wp_steps
    refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by ac_rfl), by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_seg7b_x24_ext_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1dfc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      emp
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b trapHooks 0x1dfc 0x1e00
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext decryptPrekeyClosureName
  rw [hfn_eq] at hpc ⊢
  dsimp only [tripleRatchetProgAtExt]
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_dup_ext_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b trapHooks 0x1cd8 0x1ce8
  closure_fetches_range_cli b trapHooks 0x2d58 0x2d68
  closure_fetches_range_cli b trapHooks 0x34d4 0x34d8
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext decryptPrekeyClosureName
  rw [hfn_eq] at hpc ⊢
  dsimp only [tripleRatchetProgAtExt]
  have hentry : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName +
      0x34d8#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13528)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  by_vm_steps
    wp_steps
    refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

theorem p3_err_tail_dup_a_ext_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr ssCap
    v_27c v_284 v_290 v_298
    u_250 u_258 u_370 u_378 u_384 u_38c : BitVec 64)
    (v_278 v_28c u_260 u_380 : BitVec 32)
    (hcap_ne : ssCap ≠ 0xffffffffffffffff#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = 0x8000000000000017#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
       ((s.sp + 0x250#64) ↦₆₄ u_250) ∗
       ((s.sp + 0x258#64) ↦₆₄ u_258) ∗
       ((s.sp + 0x260#64) ↦₃₂ u_260) ∗
       ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
       ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
       ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
       ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
       ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
       ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       ((s.sp + 0x384#64) ↦₆₄ u_384) ∗
       ((s.sp + 0x38c#64) ↦₆₄ u_38c))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ssCap) ∗
          ((s.sp + 0x250#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x258#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x260#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x278#64) ↦₃₂ v_278) ∗
          ((s.sp + 0x27c#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x284#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x28c#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x290#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x298#64) ↦₆₄ v_298) ∗
          ((s.sp + 0x370#64) ↦₆₄ v_27c) ∗
          ((s.sp + 0x378#64) ↦₆₄ v_284) ∗
          ((s.sp + 0x380#64) ↦₃₂ v_28c) ∗
          ((s.sp + 0x384#64) ↦₆₄ v_290) ∗
          ((s.sp + 0x38c#64) ↦₆₄ v_298)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = v_278.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_cap := cond_eq_adds64_of_ne_neg1 hcap_ne
  closure_fetches_range_cli b trapHooks 0x34dc 0x34e4
  closure_fetches_range_cli b trapHooks 0x3500 0x3504
  closure_fetches_range_cli b trapHooks 0x351c 0x3534
  closure_fetches_range_cli b trapHooks 0x3570 0x3598
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext decryptPrekeyClosureName
  rw [hfn_eq] at hpc ⊢
  dsimp only [tripleRatchetProgAtExt]
  have hentry : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName +
      0x3598#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13720)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0x8000000000000017#64 := hx28
  by_vm_steps
    wp_steps
    refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by ac_rfl), rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_tail_b_ext_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag prevStatesPtr
    w_370 w_378 w_380 w_388
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
    savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (w_22 w_390 u_ret08 u_ret2c : BitVec 32)
    (b_2c0 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWP (tripleRatchetProgAtExt b ext) retAddr s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((outPtr + 0x0#64) ↦₆₄ u_ret0) ∗
       ((outPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((outPtr + 0xc#64) ↦₆₄ u_ret0c) ∗
       ((outPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((outPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗
       ((outPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((outPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
       ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
       ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
       ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
       ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
       ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
       ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
       ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        VmPreserved s s1 ∧
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ w_370) ∗
          ((s.sp + 0x378#64) ↦₆₄ w_378) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗
          ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗
          ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗
          ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗
          ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗
          ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗
          ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗
          ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧
        s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧
        s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧
        s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧
        s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧
        s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧
        s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b trapHooks 0x359c 0x35a0
  closure_fetches_range_cli b trapHooks 0x35d0 0x35d4
  closure_fetches_range_cli b trapHooks 0x35ec 0x362c
  have hfn_eq : (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName :=
    fnAddr_tripleRatchet_eq_trapHooks b ext decryptPrekeyClosureName
  rw [hfn_eq] at hpc
  dsimp only [tripleRatchetProgAtExt]
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = w_22.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = errTag := hx28
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨by simp_all [arm64_norm], Entails.of_eq (by ac_rfl),
      by simp_all [arm64_norm], rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm]⟩

end ClosureVmBlocks

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.SetState4KBudget
