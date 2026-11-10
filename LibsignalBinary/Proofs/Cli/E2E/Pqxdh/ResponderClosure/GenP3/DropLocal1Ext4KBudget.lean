/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropVecExt4KBudget
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `dealloc`-Only `drop_session_structure_local1` on `tripleRatchetProgAtExt`

Proves `drop_session_structure_local1_of_dealloc_ext` and `drop_session_structure_local1_ok_ext_4k`
against `dropSessionStructureLocal1SpecBase M A lim` on `tripleRatchetProgAtExt b ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropVecMessageKeySpec dropVecChainSpec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget (
  AllocContractsMem4KBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropVecExt4KBudget (
  drop_vec_message_key_of_dealloc_ext drop_vec_chain_of_dealloc_ext
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropVecMessageKeySpecBase dropVecChainSpecBase
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Budget-threaded specification of `core::ptr::drop_glue::<SessionStructure> [local#1]` (`FreeOnlyEvs`, zero `FitsEnv`). -/
def dropSessionStructureLocal1SpecBase (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack

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

private theorem freeOnlyPool_intro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    A.pool lim st s ⊢ freeOnlyPool A lim st s :=
  Entails.sepExists_right [] (Entails.pure_right FreeOnlyEvs.nil (Entails.refl _))

private theorem freeOnlyPool_dealloc_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs : List AllocEvent} (hevs : FreeOnlyEvs evs)
    (sz al : Nat) (s : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) (M.stepEvents evs st)) s ⊢
      freeOnlyPool A lim st s := by
  dsimp only [freeOnlyPool]
  rw [← M.stepEvents_append evs (rustDeallocEvents sz al) st]
  exact Entails.sepExists_right (evs ++ rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.append hevs (FreeOnlyEvs.singleton al sz)) (Entails.refl _))

private theorem freeOnlyPool_append_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs1 evs2 : List AllocEvent}
    (hevs1 : FreeOnlyEvs evs1) (hevs2 : FreeOnlyEvs evs2) (s : State) :
    A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s ⊢
      freeOnlyPool A lim st s := by
  dsimp only [freeOnlyPool]
  rw [← M.stepEvents_append evs1 evs2 st]
  exact Entails.sepExists_right (evs1 ++ evs2)
    (Entails.pure_right (FreeOnlyEvs.append hevs1 hevs2) (Entails.refl _))

private theorem freeOnlyPool_sub_here {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {evs1 : List AllocEvent} (hevs1 : FreeOnlyEvs evs1)
    (s : State) :
    (∃∗ evs2 : List AllocEvent, ⌜FreeOnlyEvs evs2⌝ ∗
      A.pool lim (M.stepEvents evs2 (M.stepEvents evs1 st)) s) ⊢
      freeOnlyPool A lim st s :=
  Entails.sepExists_elim fun _ =>
    Entails.pure_left fun hevs2 => freeOnlyPool_append_here A lim st hevs1 hevs2 s

private theorem sepWP_open_freeOnlyPool {prog : Program} {target : BitVec 64} {s : State}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hfoc : P = freeOnlyPool A lim st s ∗ R)
    (hk : ∀ evs : List AllocEvent, FreeOnlyEvs evs →
      SepWP prog target s (A.pool lim (M.stepEvents evs st) s ∗ R) post) :
    SepWP prog target s P post := by
  rw [hfoc]
  dsimp only [freeOnlyPool]
  apply SepWP.of_sepExists_left
  intro evs
  rw [sepConj_assoc]
  exact SepWP.pure_elim (hk evs)

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

private theorem SepWP.seq_state {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, Pm, hPm, hent, hq⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ :=
      SepWP.to_reaches_pc (SepWP.weaken_pre hent (h2 sm hpcm hrunm hq)) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem align_pre_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  heq ▸ h

@[reducible]
private def Saved32Preserved4K (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem stackAt_ss_local1_split_4k (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal1Stack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp dropVecChainStack 4 (by decide)

private theorem stackAt_dropVecChain_split_alloc_4k (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 96 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecChainStack = allocHookStack + 96 from rfl,
      stackAt_split_bottom' fsp allocHookStack 96 (by decide)]

private theorem stackAt_dropVecChain_split_mk_4k (fsp : BitVec 64) :
    stackAt fsp dropVecChainStack =
      memRegion (fsp - 4192#64) 48 ∗ stackAt fsp dropVecMessageKeyStack := by
  rw [show dropVecChainStack = dropVecMessageKeyStack + 48 from rfl,
      stackAt_split_bottom' fsp dropVecMessageKeyStack 48 (by decide)]
  rfl

private theorem stackAt_dropVecMessageKey_split_alloc_4k (fsp : BitVec 64) :
    stackAt fsp dropVecMessageKeyStack =
      memRegion (fsp - 4144#64) 48 ∗ stackAt fsp allocHookStack := by
  rw [show dropVecMessageKeyStack = allocHookStack + 48 from rfl,
      stackAt_split_bottom' fsp allocHookStack 48 (by decide)]

private theorem tail_stack_128_from_bottom_4k (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) dropVecChainStack ∗ cells (sp - 32#64) 4 := by
  rw [← stackAt_split_bottom' sp allocHookStack 128 (by decide),
      show allocHookStack + 128 = dropSessionStructureLocal1Stack from rfl,
      ← stackAt_ss_local1_split_4k sp]

private theorem tail_dealloc_ss_local1_pre_weaken_4k (ss cap ptr : BitVec 64)
    (live rest pool : SepProp) (sp : BitVec 64) (fp lr x19 v3 : BitVec 64) :
    ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
      live ∗ rest ∗ pool ∗
      stackAt (sp - 32#64) dropVecChainStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    pool ∗ live ∗ stackAt sp allocHookStack ∗
      (memRegion (ss + 120#64) 24 ∗ rest ∗ memRegion (sp - 4224#64) 128) := by
  have h1 : ((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ⊢
      memRegion (ss + 120#64) 24 := by
    have ha1 : (ss + 120#64) + 8#64 = ss + 128#64 := by bv_omega
    have ha2 : (ss + 120#64) + 16#64 = ss + 136#64 := by bv_omega
    rw [← ha1, ← ha2]
    exact header_cells_entails_memRegion_24 (ss + 120#64) cap ptr
  have h2 :
      stackAt (sp - 32#64) dropVecChainStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_128_from_bottom_4k sp]
    cells_unfold
    refine Entails.sepExists_right fp (Entails.sepExists_right lr
      (Entails.sepExists_right x19 (Entails.sepExists_right v3 (Entails.refl _))))
  have hreord :
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8 ∗
        live ∗ rest ∗ pool ∗
        stackAt (sp - 32#64) dropVecChainStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3)) =
      (((ss + 120#64) ↦₆₄ cap) ∗ ((ss + 128#64) ↦₆₄ ptr) ∗ memRegion (ss + 136#64) 8) ∗
        (live ∗ rest ∗ pool ∗
         (stackAt (sp - 32#64) dropVecChainStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ v3))) := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private abbrev deallocCallOffSs1 : BitVec 64 :=
  bv% (ls_off% "__rustc::__rust_dealloc" -
    ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")

private abbrev mkCallOffSs1 : BitVec 64 :=
  bv% (2 ^ 64 +
    (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>") -
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))

private abbrev vcCallOffSs1 : BitVec 64 :=
  bv% (2 ^ 64 +
    (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") -
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))

private theorem fnAddr_dropVecMessageKey_eq_ss_local1_add_4k (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecMessageKeyName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + mkCallOffSs1 := by
  unfold tripleRatchetProgAtExt mkCallOffSs1
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

private theorem fnAddr_dropVecChain_eq_ss_local1_add_4k (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName =
      (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + vcCallOffSs1 := by
  unfold tripleRatchetProgAtExt vcCallOffSs1
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")]
  bv_omega

@[reducible]
private def ssSender1HeadersAt_4k (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) : SepProp :=
  ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
  ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
  ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16

private theorem ssSender1HeadersAt_entails_memRegions_4k (ss : BitVec 64) (sg : SenderChainGhost)
    (ckCap ckPtr : BitVec 64) :
    ssSender1HeadersAt_4k ss sg ckCap ckPtr ⊢
      memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 := by
  unfold ssSender1HeadersAt_4k
  have h1 := header_cells_entails_memRegion_24 (ss + 144#64) sg.srk.cap sg.srk.ptr
  have h2 := header_cells_entails_memRegion_24 (ss + 168#64) sg.priv.cap sg.priv.ptr
  have h3 := header_cells_entails_memRegion_32 (ss + 216#64) ckCap ckPtr
  have ha1 : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
  have ha2 : (ss + 144#64) + 16#64 = ss + 160#64 := by bv_omega
  have hb1 : (ss + 168#64) + 8#64 = ss + 176#64 := by bv_omega
  have hb2 : (ss + 168#64) + 16#64 = ss + 184#64 := by bv_omega
  have hc1 : (ss + 216#64) + 8#64 = ss + 224#64 := by bv_omega
  have hc2 : (ss + 216#64) + 16#64 = ss + 232#64 := by bv_omega
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  have hgroup :
      (((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8 ∗
        ((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8 ∗
        ((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16) =
      ((((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗ memRegion (ss + 160#64) 8) ∗
       (((ss + 168#64) ↦₆₄ sg.priv.cap) ∗ ((ss + 176#64) ↦₆₄ sg.priv.ptr) ∗ memRegion (ss + 184#64) 8) ∗
       (((ss + 216#64) ↦₆₄ ckCap) ∗ ((ss + 224#64) ↦₆₄ ckPtr) ∗ memRegion (ss + 232#64) 16)) := by sep_ac_rfl
  rw [hgroup,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 24) (k := 24) (b' := ss + 168#64) rfl (by bv_omega) (by decide),
      show (memRegion (ss + 144#64) 24 ∗ memRegion (ss + 168#64) 24) ∗ memRegion (ss + 216#64) 32 =
        memRegion (ss + 144#64) 24 ∗ memRegion (ss + 168#64) 24 ∗ memRegion (ss + 216#64) 32 from sepConj_assoc _ _ _]
  exact sepConj_mono h1 (sepConj_mono h2 h3)

private theorem ssSender1_memRegions_entails_104_4k (ss : BitVec 64) :
    memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32 ⊢
      memRegion (ss + 144#64) 104 := by
  have heq :
      (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) =
      (memRegion (ss + 144#64) 48 ∗ memRegion (ss + 192#64) 24 ∗ memRegion (ss + 216#64) 32) := by sep_ac_rfl
  rw [heq,
      ProofLib.memRegion_split' (b := ss + 144#64) (n := 48) (k := 56) (b' := ss + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ss + 192#64) (n := 24) (k := 32) (b' := ss + 216#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

private theorem optSenderChainAt_some_entails_ss_local1_4k (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ∃∗ ckCap : BitVec 64, ∃∗ ckPtr : BitVec 64,
        ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A ckCap ckPtr) ∗
        vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  have h := optSenderChainAt_some_entails_dealloc1 A (ss + 144#64) sg sc
  have ha1 : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
  have ha2 : (ss + 144#64) + 16#64 = ss + 160#64 := by bv_omega
  have ha3 : (ss + 144#64) + 24#64 = ss + 168#64 := by bv_omega
  have ha4 : (ss + 144#64) + 32#64 = ss + 176#64 := by bv_omega
  have ha5 : (ss + 144#64) + 40#64 = ss + 184#64 := by bv_omega
  have ha6 : (ss + 144#64) + 48#64 = ss + 192#64 := by bv_omega
  have ha7 : (ss + 144#64) + 72#64 = ss + 216#64 := by bv_omega
  have ha8 : (ss + 144#64) + 80#64 = ss + 224#64 := by bv_omega
  have ha9 : (ss + 144#64) + 88#64 = ss + 232#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at h
  refine Entails.trans h ?_
  apply Entails.sepExists_elim; intro ckCap; refine Entails.sepExists_right ckCap ?_
  apply Entails.sepExists_elim; intro ckPtr; refine Entails.sepExists_right ckPtr ?_
  unfold ssSender1HeadersAt_4k
  exact Entails.of_eq (by sep_ac_rfl)

private theorem drop_ss_local1_first3_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + deallocCallOffSs1)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 12#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 76#64)
        s
        ((ssFirst3HeadersAt_shared_lb ss G ∗
          vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc G.root) ∗
          freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name, deallocCallOffSs1,
    BitVec.ofNat_eq_ofNat] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 12 64
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" = entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := entry + 36#64) (P_mid := fun sm =>
    (ssFirst3HeadersAt_shared_lb ss G ∗
      vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A.repAlloc G.root) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 36#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + deallocCallOffSs1)
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.localIk.cap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := entry + 56#64) (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 56#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + deallocCallOffSs1)
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.remoteIk.cap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 76#64) s2
          ((ssFirst3HeadersAt_shared_lb ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
            freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt_shared_lb ss G ∗ freeOnlyPool A lim st sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 76#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + deallocCallOffSs1)
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.root.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss_local1_sender_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + deallocCallOffSs1)
      (rustCliDeallocBudgetSpecBase M A lim))
    (hdrop_mk : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + mkCallOffSs1)
      (dropVecMessageKeySpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 76#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 156#64)
        s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          freeOnlyPool A lim st s ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  simp only [dropVecMessageKeySpecBase] at hdrop_mk
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name, deallocCallOffSs1,
    mkCallOffSs1, BitVec.ofNat_eq_ofNat] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 76 80
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" = entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A.repAlloc (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt
        have ha : (ss + 144#64) + 8#64 = ss + 152#64 := by bv_omega
        rw [ha]
      rw [hnone]
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 156#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            freeOnlyPool A lim st s ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              freeOnlyPool A lim st sm ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps_sync_pool (entry + 156#64)
        wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      have ha : ss + 152#64 = (ss + 144#64) + 8#64 := by bv_omega
      rw [ha]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_shared_lb (ss + 144#64))
    | some _ =>
      simp only [optSenderChainAt]
      exact DropsCommon.SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact DropsCommon.SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_entails_ss_local1_4k A.repAlloc ss sg sc)) ?_
      wp_pull_exists
      rename_i ckCap ckPtr
      refine SepWP.pure_elim ?_
      intro hcmn
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      nth_rw 1 [stackAt_dropVecMessageKey_split_alloc_4k fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A.repAlloc ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
        freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (Entails.of_eq (by dsimp only [ssSender1HeadersAt_4k]; sep_ac_rfl)) ?_
      refine SepWP.seq_state (mid := entry + 104#64) (P_mid := fun sm =>
        (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
          vecPinDealloc A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 4144#64) 48 ∗ Frame))
        (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
        ?_ ?_
      · dsimp only [ssSender1HeadersAt_4k, vecPinDealloc, sgnPinDealloc]
        by_cases hcap : (sg.srk.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 104#64)
          refine align_pre_state (by sep_ac_rfl) ?_
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + deallocCallOffSs1)
          wp_call hdealloc (sg.srk.ptr, sg.srk.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs sg.srk.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
          wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine SepWP.seq_state (mid := entry + 124#64) (P_mid := fun sm =>
          (ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗ sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
          freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
          (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 4144#64) 48 ∗ Frame))
          (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
          ?_ ?_
        · dsimp only [ssSender1HeadersAt_4k, vecPinDealloc, sgnPinDealloc]
          by_cases hcap : (sg.priv.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
          · wp_steps_sync_pool (entry + 124#64)
            wp_done
          · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            wp_steps_sync_pool (entry + deallocCallOffSs1)
            wp_call hdealloc (sg.priv.ptr, sg.priv.cap.toNat, 1, M.stepEvents evs st)
            have _htr_d := ‹AllocCallPreserved _ sf›.2.1
            apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs sg.priv.cap.toNat 1 sf) (by sep_focus)
            refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine SepWP.seq_state (mid := entry + 148#64) (P_mid := fun sm =>
            vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp dropVecMessageKeyStack ∗
            ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
            ?_ ?_
          · have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 148#64) s2
                ((ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗ sgnPinDealloc A.repAlloc ckCap ckPtr) ∗
                  freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 4144#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt_4k ss sg ckCap ckPtr ∗
                    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
                    (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 4144#64) 48 ∗ Frame)) ∧
                  Saved32Preserved4K s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              dsimp only [ssSender1HeadersAt_4k, sgnPinDealloc]
              by_cases hcap : ckCap.slt 1#64 = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
              · wp_steps_sync_pool (entry + 148#64)
                wp_done
              · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
                wp_steps_sync_pool (entry + deallocCallOffSs1)
                wp_call hdealloc (ckPtr, ckCap.toNat, 1, M.stepEvents evs st)
                have _htr_d := ‹AllocCallPreserved _ sf›.2.1
                apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs ckCap.toNat 1 sf) (by sep_focus)
                refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_4k ss sg ckCap ckPtr)) ?_
            rw [stackAt_dropVecMessageKey_split_alloc_4k fsp]
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 156#64) s3
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  freeOnlyPool A lim st s3 ∗ stackAt fsp dropVecMessageKeyStack ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗
                    freeOnlyPool A lim st sm ∗ stackAt fsp dropVecMessageKeyStack ∗ Frame) ∧
                  Saved32Preserved4K s0 sm fsp ∧
                  sm.readReg64 .x19 = ss) := by
              refine sepWP_open_freeOnlyPool (by sep_focus) fun evs1 hevs1 => ?_
              wp_steps_sync_pool (entry + mkCallOffSs1)
              wp_call hdrop_mk (⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩, M.stepEvents evs1 st)
              first
              | apply SepWP.fold (freeOnlyPool_sub_here A lim st hevs1 sf) (by sep_focus)
              | apply SepWP.fold (freeOnlyPool_append_here A lim st hevs1 ‹_› sf) (by sep_focus)
              refine align_pre_state (by rw [hsp_3]; sep_ac_rfl) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            exact sepConj_mono_left (ssSender1_memRegions_entails_104_4k ss)

private theorem drop_ss_local1_tail3_4k {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + deallocCallOffSs1)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 164#64 →
      s.status = .Running →
      Saved32Preserved4K s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + 232#64)
        s
        ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗ memRegion (ss + 96#64) 24) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32Preserved4K s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  have hfn : libsignalSessionCode.fnOff dropSessionStructureLocal1Name =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") :=
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name, deallocCallOffSs1,
    BitVec.ofNat_eq_ofNat] at *
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 164 68
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" = entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := entry + 188#64) (P_mid := fun sm =>
    (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A.repAlloc kCap kPtr ∗
      vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 188#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + deallocCallOffSs1)
      wp_call hdealloc (pPtr, pCap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pCap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := entry + 212#64) (P_mid := fun sm =>
      (ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved32Preserved4K s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt_shared_lb, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 212#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + deallocCallOffSs1)
        wp_call hdealloc (kPtr, kCap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs kCap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 232#64) s2
          ((ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt_shared_lb ss pCap pPtr kCap kPtr G ∗
              freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32Preserved4K s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt_shared_lb, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 232#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + deallocCallOffSs1)
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.alice.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

private def ss1InnerSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (memRegion (x.ss + 120#64) 24 ∗ memRegion x.ss 24 ∗ memRegion (x.ss + 24#64) 24 ∗
        memRegion (x.ss + 48#64) 24 ∗ memRegion (x.ss + 72#64) 24 ∗ memRegion (x.ss + 96#64) 24 ∗
        memRegion (x.ss + 144#64) 104 ∗ memRegion (x.ss + 248#64) 48 ∗
        memRegion (x.ss + 296#64) 32 ∗ memRegion (x.ss + 328#64) 16) ∗
      freeOnlyPool A lim st sf ∗
      stackAt s0.sp dropSessionStructureLocal1Stack

set_option maxHeartbeats 1200000 in
private theorem drop_session_structure_local1_inner_of_dealloc_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (ss1InnerSpec M A lim) := by
  simp only [ss1InnerSpec]
  have hfn := (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")
  have hdealloc_raw :
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + deallocCallOffSs1)
        (rustCliDeallocBudgetSpecBase M A lim) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName)
      (spec := rustCliDeallocBudgetSpecBase M A lim) hdc
      dropSessionStructureLocal1Name
      (num% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"))
      (by fnoff_eq)
  have hdrop_mk_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + mkCallOffSs1)
      (dropVecMessageKeySpecBase M A lim) := by
    rw [← fnAddr_dropVecMessageKey_eq_ss_local1_add_4k]
    exact drop_vec_message_key_of_dealloc_ext hdc
  have hdrop_vc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name + vcCallOffSs1)
      (dropVecChainSpecBase M A lim) := by
    rw [← fnAddr_dropVecChain_eq_ss_local1_add_4k]
    exact drop_vec_chain_of_dealloc_ext hdc
  clear hdc
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 156 8
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    trapHooks hfn
    (num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]")) 232 40
  clear hfn
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  have hdrop_vc := hdrop_vc_raw
  simp only [dropVecChainSpecBase] at hdrop_vc
  have hfirst3 := drop_ss_local1_first3_4k (b := b) (ext := ext) hdealloc_raw
  have hsender := drop_ss_local1_sender_4k (b := b) (ext := ext) hdealloc_raw hdrop_mk_raw
  have htail3 := drop_ss_local1_tail3_4k (b := b) (ext := ext) hdealloc_raw
  clear hdealloc_raw hdrop_mk_raw hdrop_vc_raw
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name] at hfirst3 hsender htail3
  dsimp only [tripleRatchetProgAtExt, dropSessionStructureLocal1Name, deallocCallOffSs1,
    vcCallOffSs1, BitVec.ofNat_eq_ofNat] at hdrop_vc hdealloc ⊢
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨ss, G, sessSt⟩, st⟩
  dsimp only at h hpre ⊢
  subst h
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split_4k s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G sessSt)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine SepWP.seq_state (mid := entry + 12#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip sessSt.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4224#64) 96 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
    (Q := fun sm =>
      Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
    rw [hsp_sub]
    wp_steps_sync_pool (entry + 12#64)
    apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
    refine align_pre_state
      (by dsimp only [ssFirst3HeadersAt_shared_lb, ssTail3HeadersAt_shared_lb,
            Reg.x19, Reg.lr, Reg.fp]; sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine SepWP.seq_state (mid := entry + 76#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStack ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip sessSt.receiverChains) ∗
        (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4224#64) 48 ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
      (Q := fun sm =>
        Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt_shared_lb]; simp only [sepConj_assoc]; refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKey_split_alloc_4k (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 4144#64 = s0.sp - 4176#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 4224#64) (n := 48) (k := 48)
            (b' := s0.sp - 4176#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2⟩
      refine SepWP.seq_state (mid := entry + 156#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip sessSt.receiverChains) ∗
          freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
          ((ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            sgnPinDealloc A.repAlloc pCap pPtr ∗
            sgnPinDealloc A.repAlloc kCap kPtr ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
        (Q := fun sm =>
          Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align
            G.sender sessSt.senderChain s2 _ hpc2 hrun2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChain_split_mk_4k (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
        rw [hsp_sub2]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s3 hpc3 hrun3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine SepWP.seq_state (mid := entry + 164#64)
          (P_mid := fun sm =>
            (ssTail3HeadersAt_shared_lb (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
              sgnPinDealloc A.repAlloc pCap pPtr ∗
              sgnPinDealloc A.repAlloc kCap kPtr ∗
              vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
            (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 4224#64) 96 ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
          (Q := fun sm =>
            Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
          ?_ ?_
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs1 hevs1 => ?_
          wp_steps_sync_pool (entry + vcCallOffSs1)
          wp_call hdrop_vc (⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr,
            G.chains.zip sessSt.receiverChains⟩, M.stepEvents evs1 st)
          first
          | apply SepWP.fold (freeOnlyPool_sub_here A lim st hevs1 sf) (by sep_focus)
          | apply SepWP.fold (freeOnlyPool_append_here A lim st hevs1 ‹_› sf) (by sep_focus)
          refine align_pre_state ?_ ?_
          · rw [hsp_3, stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
            rw [hsp_sub3]
            dsimp only [ssTail3HeadersAt_shared_lb]
            sep_ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
          refine SepWP.seq_state (mid := entry + 232#64)
            (P_mid := fun sm =>
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
              freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 32#64) dropVecChainStack ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3))
            (Q := fun sm =>
              Saved32Preserved4K s0 sm (s0.sp - 32#64) ∧
              sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · dsimp only [ssTail3HeadersAt_shared_lb]; simp only [sepConj_assoc]; refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align
                pCap pPtr kCap kPtr G s4 _ hpc4 hrun4 hpres4 hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChain_split_alloc_4k (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 4192#64 = s0.sp - 4224#64 := by bv_omega
            rw [hsp_sub4]
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s5 hpc5 hrun5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [vecPinDealloc]
            by_cases hcap : (G.pq.cap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
            · wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
              refine SepWP.weaken_pre
                (pq_header24_weaken_shared_lb (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
              wp_done
            · wp_steps_sync_pool (entry + deallocCallOffSs1)
              refine SepWP.weaken_pre
                (tail_dealloc_ss_local1_pre_weaken_4k (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  _ _ (freeOnlyPool A lim st _) s0.sp _ _ _ _) ?_
              refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
              wp_call hdealloc (G.pq.ptr, G.pq.cap.toNat, 1, M.stepEvents evs st)
              have _htr_d := ‹AllocCallPreserved _ sf›.2.1
              apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.pq.cap.toNat 1 sf)
                (by sep_focus)
              refine SepWP.weaken_pre (P' :=
                (memRegion (s0.readReg64 (Reg.gpr 0#5) + 120#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 96#64) 24 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 248#64) 48 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 296#64) 32 ∗
                  memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16) ∗
                freeOnlyPool A lim st sf ∗
                (stackAt (s0.sp - 32#64) dropVecChainStack ∗ cells (s0.sp - 32#64) 4))
                (by rw [← tail_stack_128_from_bottom_4k s0.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
              cells_unfold
              wp_pull_exists
              wp_done

/-- `core::ptr::drop_glue::<SessionStructure> [local#1]` meets `dropSessionStructureLocal1SpecBase M A lim`
on `tripleRatchetProgAtExt b ext` assuming only `dealloc`. -/
theorem drop_session_structure_local1_of_dealloc_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp =>
    (drop_session_structure_local1_inner_of_dealloc_ext hdc).mono_outcome (x, st) R s0 hpc hrun
      hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ss1InnerSpec, dropSessionStructureLocal1SpecBase] at hpost ⊢
    have hreg :
        (memRegion (x.ss + 120#64) 24 ∗ memRegion x.ss 24 ∗ memRegion (x.ss + 24#64) 24 ∗
          memRegion (x.ss + 48#64) 24 ∗ memRegion (x.ss + 72#64) 24 ∗ memRegion (x.ss + 96#64) 24 ∗
          memRegion (x.ss + 144#64) 104 ∗ memRegion (x.ss + 248#64) 48 ∗
          memRegion (x.ss + 296#64) 32 ∗ memRegion (x.ss + 328#64) 16) ⊢ memRegion x.ss 344 :=
      Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (session_memRegions_entails_344_shared_lb x.ss)
    have hpost1 : sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗
        freeOnlyPool A lim st sf ∗
        stackAt s0.sp dropSessionStructureLocal1Stack) ∗ R :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hreg))) hpost
    unfold freeOnlyPool at hpost1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨htr, hpost1⟩
    have hpost2 : sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (memRegion x.ss 344 ∗ stackAt s0.sp dropSessionStructureLocal1Stack ∗ R) := by
      convert hpost1 using 1
      sep_ac_rfl
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost2
    rcases hpost2 with ⟨evs, hpost2⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost2
    rcases hpost2 with ⟨hevs, hpost2⟩
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    convert hpost2 using 1
    sep_ac_rfl
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- `core::ptr::drop_glue::<SessionStructure> [local#1]` meets `dropSessionStructureLocal1SpecBase M A lim`
under `AllocContractsMem4KBudget b M A lim ext`. -/
theorem drop_session_structure_local1_ok_ext_4k
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim) :=
  drop_session_structure_local1_of_dealloc_ext hA.dealloc

theorem drop_session_structure_local1_ok_ext
    {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1SpecBase M A lim) :=
  drop_session_structure_local1_of_dealloc_ext hA.dealloc

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4KBudget
