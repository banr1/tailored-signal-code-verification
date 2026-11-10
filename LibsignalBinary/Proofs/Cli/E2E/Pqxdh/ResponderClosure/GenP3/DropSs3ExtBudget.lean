/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Helpers
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `ext`-Parameterized `drop_session_structure3_ok_ext`

Proves `drop_session_structure3_of_dealloc_ext` and `drop_session_structure3_ok_ext` against
`dropSessionStructureLocal2SpecBase M A lim` on `tripleRatchetProgAtExt b ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ReceiverChain SenderChain)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecAt)
open CryptoVerification.LibsignalSessionRepr (ChainGhost chainAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SenderChainGhost SessionGhost noneCap optSenderChainAt sessionStateAt)
open CryptoVerification.LibsignalTripleRatchet (deallocName sub_ok_at_of_fnAddr tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropChainStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (DropSessionStructureGhost dropSessionStructureLocal2Stack)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Helpers (
  Saved48Preserved chainAt_of_exposed_sender chains_header24_weaken cons_len_mul
  fnAddr_dropChain_eq_ss2_add_ext ofNat_add_one_beq_one_false ofNat_beq_zero_false
  ofNat_succ_eq_add_one optSenderChainAt_some_expose post_loop_weaken_at_72
  pq_header24_weaken sender_none_entails_memRegion_104 sep_pull_body sep_push_body
  sep_rejoin_loop sessionStateAt_entails_dealloc session_memRegions_entails_344
  sgnPinDealloc ssFirst3HeadersAt ssFirst3HeadersAt_entails_memRegions
  ssTail3HeadersAt ssTail3HeadersAt_entails_memRegions stackAt_dropChain_split_alloc
  stackAt_ss2_split tail_dealloc_ss2_pre_weaken tail_len_mul_lt
  tail_stack_ss2_96_from_bottom vecAt_expose_loop_at_72 vecPinDealloc)
open LibsignalBinary.Heap (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpecBase rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget (AllocContractsMem4KBudget dealloc_ok_at_ext)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget (drop_chain2_of_dealloc_ext drop_proto_chain2_of_dealloc_ext)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropChainSpecBase dropProtoChainSpecBase)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Budget-threaded specification of `core::ptr::drop_glue::<SessionStructure> [local#4]` (`FreeOnlyEvs`, zero `FitsEnv`). -/
def dropSessionStructureLocal2SpecBase (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
        memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp dropSessionStructureLocal2Stack

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
      refine SepWP.done (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm, *])
        (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm, *])
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

private abbrev deallocCallOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64)

private abbrev dropChainCallOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64)

private theorem drop_ss2_first3_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 80#64)
        s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDealloc A.repAlloc G.root) ∗
          freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSs3BinCli b trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 276
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro G s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := entry + 40#64) (P_mid := fun sm =>
    (ssFirst3HeadersAt ss G ∗
      vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
      vecPinDealloc A.repAlloc G.root) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
    by_cases hcap : (G.localIk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 40#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      wp_call hdealloc (G.localIk.ptr, G.localIk.cap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.localIk.cap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := entry + 60#64) (P_mid := fun sm =>
      (ssFirst3HeadersAt ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt, vecPinDealloc]
      by_cases hcap : (G.remoteIk.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 60#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
        wp_call hdealloc (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.remoteIk.cap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 80#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDealloc A.repAlloc G.root) ∗
            freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ freeOnlyPool A lim st sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssFirst3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.root.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 80#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
          wp_call hdealloc (G.root.ptr, G.root.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.root.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions ss G)), h.2⟩)

private theorem drop_ss2_sender_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        dropChainCallOff)
      (dropProtoChainSpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 80#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 100#64)
        s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          freeOnlyPool A lim st s ∗ stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [dropProtoChainSpecBase] at hdrop_chain
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name,
    dropChainCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSs3BinCli b trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 276
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro senderG senderSt s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      unfold optSenderChainAt
      have hstep : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 100#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
            freeOnlyPool A lim st s ∗ stackAt fsp dropChainStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion ((ss + 144#64) + 8#64) 96) ∗
              freeOnlyPool A lim st sm ∗ stackAt fsp dropChainStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps_sync_pool (entry + 100#64)
        wp_done
      exact SepWP.mono hstep (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (sender_none_entails_memRegion_104 (ss + 144#64))),
          h.2⟩)
    | some _ =>
      simp only [optSenderChainAt]
      exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Helpers.SepWP.false_elim_left
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Helpers.SepWP.false_elim_left
    | some sc =>
      refine SepWP.weaken_pre (sepConj_mono_left (optSenderChainAt_some_expose A.repAlloc
        (ss + 144#64) sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hpk, hlen, hcap_lt, hptr_ne, hcmn⟩
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      refine sepWP_open_freeOnlyPool (by sep_focus) fun evs1 hevs1 => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 +
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      have hch_ent := chainAt_of_exposed_sender A.repAlloc
        (ss + 144#64) sg sc hpk hlen hcap_lt hptr_ne
      apply SepWP.fold hch_ent (by sep_focus)
      wp_call hdrop_chain (⟨ss + 144#64, (⟨sg.srk, sg.priv, sg.mkCap, sg.mkPtr, [], sg.ck⟩,
        ⟨sc.ratchetKey.publicKey, some sc.chainKey, []⟩)⟩, M.stepEvents evs1 st)
      first
      | apply SepWP.fold (freeOnlyPool_sub_here A lim st hevs1 sf) (by sep_focus)
      | apply SepWP.fold (freeOnlyPool_append_here A lim st hevs1 ‹_› sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done

set_option maxHeartbeats 800000 in
private theorem drop_ss2_receiver_loop_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdrop_chain : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        dropChainCallOff)
      (dropChainSpecBase M A lim))
    (s0 : State) (fsp ss ptr : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      s.readReg64 .x20 = ptr →
      s.readReg64 .x21 = cur →
      s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 132#64)
        s
        (arrayAt (chainAt A.repAlloc) 104 cur rest ∗ freeOnlyPool A lim st s ∗
          stackAt fsp dropChainStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp dropChainStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss ∧
          sm.readReg64 .x20 = ptr) := by
  simp only [dropChainSpecBase] at hdrop_chain
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name,
    dropChainCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSs3BinCli b trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 276
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
    rw [show arrayAt (chainAt A.repAlloc) 104 cur ((g, c) :: tl) =
          chainAt A.repAlloc (g, c) cur ∗ arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine SepWP.seq_state (mid := entry + 120#64)
      (P_mid := fun sm => memRegion cur 104 ∗ freeOnlyPool A lim st sm ∗ stackAt fsp dropChainStack ∗
        (arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ss ∧ sm.readReg64 .x20 = ptr ∧
        sm.readReg64 .x21 = cur ∧ sm.readReg64 .x22 = BitVec.ofNat 64 ((g, c) :: tl).length)
      ?_ ?_
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs1 hevs1 => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 +
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
        ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") % 2^64))
      wp_call hdrop_chain (⟨cur, (g, c)⟩, M.stepEvents evs1 st)
      first
      | apply SepWP.fold (freeOnlyPool_sub_here A lim st hevs1 sf) (by sep_focus)
      | apply SepWP.fold (freeOnlyPool_append_here A lim st hevs1 ‹_› sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩,
      hx19_1, hx20_1, hx21_1, hx22_1⟩
      cases tl with
      | nil =>
        simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
          arrayAt, emp_sepConj] at hx22_1 ⊢
        wp_steps_sync_pool (entry + 132#64)
        wp_done
      | cons hd2 tl2 =>
        have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
        have htl_len := tail_len_mul_lt hlen
        rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
            ofNat_succ_eq_add_one] at hx22_1
        have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
        have hpc_next : (BitVec.ofNat 64 (hd2 :: tl2).length + 1#64 != 1#64) = true := by
          rw [bne_iff_ne]
          intro h
          exact hne1 (beq_iff_eq.mpr h)
        wp_steps_sync_pool (entry + 112#64)
        rw [sep_push_body]
        refine SepWP.mono
          (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
            htl_ne htl_len _hpcm _hrunm
            ⟨by simpa [wp_norm, arm64_norm] using hx23_1,
             by simpa [wp_norm, arm64_norm] using hx24_1,
             by simpa [wp_norm, arm64_norm] using hx25_1,
             by simpa [wp_norm, arm64_norm] using hx26_1,
             by simpa [wp_norm, arm64_norm] using hx27_1,
             by simpa [wp_norm, arm64_norm] using hx28_1,
             by simpa [wp_norm, arm64_norm] using hsp_1,
             by simpa [wp_norm, arm64_norm] using htrace_1,
             by simpa [wp_norm, arm64_norm] using hvregs_1⟩
            (by simpa [wp_norm, arm64_norm] using hx19_1)
            (by simpa [wp_norm, arm64_norm] using hx20_1)
            (by simp [wp_norm, arm64_norm, hx21_1])
            (by simp [wp_norm, arm64_norm, hx22_1])) ?_
        intro sf Pf _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
        have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit,
          ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
        exact Entails.refl _

set_option maxHeartbeats 800000 in
private theorem drop_ss2_tail3_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp ss : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (pCap pPtr kCap kPtr : BitVec 64) (G : SessionGhost) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 160#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ss →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name + 228#64)
        s
        ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗
            memRegion (ss + 96#64) 24) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ss) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSs3BinCli b trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 276
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  intro pCap pPtr kCap kPtr G s Frame hpc hrun hpres hx19
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.seq_state (mid := entry + 184#64) (P_mid := fun sm =>
    (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
      sgnPinDealloc A.repAlloc kCap kPtr ∗
      vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
    ?_ ?_
  · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
    by_cases hcap : pCap.slt 1#64 = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 184#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      wp_call hdealloc (pPtr, pCap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pCap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := entry + 208#64) (P_mid := fun sm =>
      (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss)
      ?_ ?_
    · dsimp only [ssTail3HeadersAt, sgnPinDealloc, vecPinDealloc]
      by_cases hcap : kCap.slt 1#64 = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 208#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
        wp_call hdealloc (kPtr, kCap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs kCap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 228#64) s2
          ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
            freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗ freeOnlyPool A lim st sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = ss) := by
        dsimp only [ssTail3HeadersAt, vecPinDealloc]
        by_cases hcap : (G.alice.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 228#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
          wp_call hdealloc (G.alice.ptr, G.alice.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs G.alice.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (ssTail3HeadersAt_entails_memRegions ss pCap pPtr kCap kPtr G)), h.2⟩)

private def ss2InnerSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureGhost × M.σ) where
  pre := (dropSessionStructureLocal2SpecBase M A lim).pre
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (memRegion x.ss 24 ∗ memRegion (x.ss + 24#64) 24 ∗ memRegion (x.ss + 48#64) 24 ∗
        memRegion (x.ss + 72#64) 24 ∗ memRegion (x.ss + 96#64) 24 ∗
        memRegion (x.ss + 120#64) 24 ∗ memRegion (x.ss + 144#64) 104 ∗
        memRegion (x.ss + 248#64) 48 ∗ memRegion (x.ss + 296#64) 32 ∗
        memRegion (x.ss + 328#64) 16) ∗
      freeOnlyPool A lim st sf ∗
      stackAt s0.sp dropSessionStructureLocal2Stack

set_option maxHeartbeats 1200000 in
private theorem drop_session_structure3_inner_of_dealloc_ext {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (ss2InnerSpec M A lim) := by
  have hdc := drop_chain2_of_dealloc_ext (b := b) hdealloc_fn
  simp only [ss2InnerSpec, dropSessionStructureLocal2SpecBase]
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName) hdealloc_fn
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name
      (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
      (by fnoff_eq)
  have hdrop_chain_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        dropChainCallOff)
      (dropChainSpecBase M A lim) := by
    dsimp only [dropChainCallOff]
    rw [← fnAddr_dropChain_eq_ss2_add_ext]
    exact hdc
  have hdrop_proto_chain_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name +
        dropChainCallOff)
      (dropProtoChainSpecBase M A lim) := by
    dsimp only [dropChainCallOff]
    rw [← fnAddr_dropChain_eq_ss2_add_ext]
    exact drop_proto_chain2_of_dealloc_ext hdealloc_fn
  clear hdc hdealloc_fn
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  have hfirst3 := drop_ss2_first3_ext (b := b) (ext := ext) hdealloc_raw
  have hsender := drop_ss2_sender_ext (b := b) (ext := ext) hdrop_proto_chain_raw
  have hloop := drop_ss2_receiver_loop_ext (b := b) (ext := ext) hdrop_chain_raw
  have htail3 := drop_ss2_tail3_ext (b := b) (ext := ext) hdealloc_raw
  clear hdealloc_raw hdrop_chain_raw hdrop_proto_chain_raw
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSs3BinCli b trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") 276
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name,
    deallocCallOff, dropChainCallOff, BitVec.ofNat_eq_ofNat] at hfirst3 hsender hloop htail3 hdealloc ⊢
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨ss, G, sessSt⟩, st⟩
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  rw [stackAt_ss2_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (sessionStateAt_entails_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G sessSt)) ?_
  wp_pull_exists
  rename_i pCap pPtr kCap kPtr
  refine SepWP.seq_state (mid := entry + 16#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDealloc A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDealloc A.repAlloc G.root) ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip sessSt.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          sgnPinDealloc A.repAlloc pCap pPtr ∗
          sgnPinDealloc A.repAlloc kCap kPtr ∗
          vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 4192#64) 48 ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
    have hsp_sub : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
    rw [hsp_sub]
    wp_steps_sync_pool (entry + 16#64)
    apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
    refine align_pre_state
      (by dsimp only [ssFirst3HeadersAt, ssTail3HeadersAt, Reg.x19, Reg.x20,
            Reg.x21, Reg.x22, Reg.lr, Reg.fp]; sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine SepWP.seq_state (mid := entry + 80#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender sessSt.senderChain ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip sessSt.receiverChains) ∗
        (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · dsimp only [ssFirst3HeadersAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      refine SepWP.mono
        (hfirst3 s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align G s1 _
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
      have hsp_sub1 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
      rw [hsp_sub1]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2⟩
      refine SepWP.seq_state (mid := entry + 100#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64) G.chainsCap G.chainsPtr
            (G.chains.zip sessSt.receiverChains) ∗
          (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
          freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 48#64) (s0.readReg64
            (Reg.gpr 0#5)) st hfsp_align G.sender sessSt.senderChain s2 _
            hpc2 hrun2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by sep_ac_rfl)), h.2⟩
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩,
        hx19_3⟩
        refine SepWP.weaken_pre
          (sepConj_mono_left (vecAt_expose_loop_at_72 A.repAlloc 104 8 (chainAt A.repAlloc)
            (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              (G.chains.zip sessSt.receiverChains))) ?_
        rw [sepConj_assoc]
        refine SepWP.pure_elim ?_
        rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
        generalize G.chains.zip sessSt.receiverChains = cs at hlen_le hlen_lt ⊢
        refine SepWP.seq_state (mid := entry + 132#64)
          (P_mid := fun sm =>
            ((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            memRegion G.chainsPtr (cs.length * 104) ∗
            (if G.chainsCap = 0 then emp
             else A.repAlloc.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
               memRegion (G.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((G.chainsCap.toNat - cs.length) * 104)) ∗
            (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
            freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          (Q := fun sm =>
            Saved48Preserved s0 sm (s0.sp - 48#64) ∧
            sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
            sm.readReg64 .x20 = G.chainsPtr)
          ?_ ?_
        · cases cs with
          | nil =>
            simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
            wp_steps_sync_pool (entry + 132#64)
            refine align_pre_state (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
            wp_done
          | cons hd tl =>
            have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
            wp_steps_sync_pool (entry + 112#64)
            refine SepWP.weaken_pre (P' :=
              arrayAt (chainAt A.repAlloc) 104 G.chainsPtr (hd :: tl) ∗
              freeOnlyPool A lim st _ ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
              (((s0.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ G.chainsCap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ G.chainsPtr) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                (if G.chainsCap = 0 then emp
                 else A.repAlloc.live G.chainsPtr (G.chainsCap.toNat * 104) 8 ∗
                   memRegion (G.chainsPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                     ((G.chainsCap.toNat - (hd :: tl).length) * 104)) ∗
                (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
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
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
              (Entails.of_eq (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl)) ?_
            refine SepWP.mono
              (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) G.chainsPtr st hfsp_align
                (hd :: tl) G.chainsPtr _ _
                (List.cons_ne_nil _ _) hlen_lt _hpcm _hrunm
                ⟨by simpa [wp_norm, arm64_norm] using hx23_3,
                 by simpa [wp_norm, arm64_norm] using hx24_3,
                 by simpa [wp_norm, arm64_norm] using hx25_3,
                 by simpa [wp_norm, arm64_norm] using hx26_3,
                 by simpa [wp_norm, arm64_norm] using hx27_3,
                 by simpa [wp_norm, arm64_norm] using hx28_3,
                 by simpa [wp_norm, arm64_norm] using hsp_3,
                 by simpa [wp_norm, arm64_norm] using htrace_3,
                 by simpa [wp_norm, arm64_norm] using hvregs_3⟩
                (by simpa [wp_norm, arm64_norm] using hx19_3)
                (by simp [wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm])
                (by simp [wp_norm, arm64_norm])) ?_
            intro sm Pm _ _ h
            exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl)),
              h.2⟩
        · intro sm hpcm hrunm ⟨⟨hx23_m, hx24_m, hx25_m, hx26_m, hx27_m, hx28_m, hsp_m, htrace_m, hvregs_m⟩,
          hx19_m, hx20_m⟩
          refine SepWP.weaken_pre
            (post_loop_weaken_at_72 A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr
              cs.length hlen_le hcap_lt _) ?_
          refine SepWP.seq_state (mid := entry + 160#64)
            (P_mid := fun sm' =>
              (ssTail3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
                sgnPinDealloc A.repAlloc pCap pPtr ∗
                sgnPinDealloc A.repAlloc kCap kPtr ∗
                vecPinDealloc A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
              freeOnlyPool A lim st sm' ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
              ((((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
                ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDealloc A.repAlloc G.pq) ∗
              (memRegion (s0.readReg64 (Reg.gpr 0#5)) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 24#64) 24 ∗
                memRegion (s0.readReg64 (Reg.gpr 0#5) + 48#64) 24) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
              memRegion (s0.sp - 4192#64) 48 ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
              ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
              ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
            (Q := fun sm' =>
              Saved48Preserved s0 sm' (s0.sp - 48#64) ∧
              sm'.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
            ?_ ?_
          · rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
            have hsp_subm : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
            rw [hsp_subm]
            by_cases hcap : (G.chainsCap == 0#64) = true <;>
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
            · wp_steps_sync_pool (entry + 160#64)
              refine SepWP.weaken_pre
                (chains_header24_weaken (s0.readReg64 (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _) ?_
              refine align_pre_state (by dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
              wp_done
            · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
              wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
                (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
              have hmul : 104#64 * G.chainsCap = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by
                bv_omega
              have hmul2 : G.chainsCap * 104#64 = BitVec.ofNat 64 (G.chainsCap.toNat * 104) := by
                bv_omega
              wp_call hdealloc (G.chainsPtr, G.chainsCap.toNat * 104, 8, M.stepEvents evs st)
              have _htr_d := ‹AllocCallPreserved _ sf›.2.1
              apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs (G.chainsCap.toNat * 104) 8 sf)
                (by sep_focus)
              refine SepWP.weaken_pre
                (sepConj_mono_right (sepConj_mono_right
                  (chains_header24_weaken (s0.readReg64
                    (Reg.gpr 0#5)) G.chainsCap G.chainsPtr _))) ?_
              refine align_pre_state (by rw [hsp_m]; dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
              wp_done
          · intro s4 hpc4 hrun4 ⟨hpres4, hx19_4⟩
            refine SepWP.seq_state (mid := entry + 228#64)
              (P_mid := fun sm' =>
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
                freeOnlyPool A lim st sm' ∗ stackAt (s0.sp - 48#64) dropChainStack ∗
                ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
              (Q := fun sm' =>
                Saved48Preserved s0 sm' (s0.sp - 48#64) ∧
                sm'.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
              ?_ ?_
            · dsimp only [ssTail3HeadersAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
              refine SepWP.mono
                (htail3 s0 (s0.sp - 48#64) (s0.readReg64
                  (Reg.gpr 0#5)) st hfsp_align pCap pPtr kCap kPtr G s4 _
                  hpc4 hrun4 hpres4 hx19_4) ?_
              intro sm' Pm _ _ h
              refine ⟨Entails.trans h.1 ?_, h.2⟩
              rw [stackAt_dropChain_split_alloc (s0.sp - 48#64)]
              have hsp_sub4 : (s0.sp - 48#64) - 4144#64 = s0.sp - 4192#64 := by bv_omega
              rw [hsp_sub4]
              exact Entails.of_eq (by sep_ac_rfl)
            · intro s5 hpc5 hrun5 ⟨⟨hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5,
              htrace_5, hvregs_5⟩, hx19_5⟩
              dsimp only [vecPinDealloc]
              by_cases hcap : (G.pq.cap == 0#64) = true <;>
                simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
              · wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
                refine SepWP.weaken_pre (pq_header24_weaken (s0.readReg64
                  (Reg.gpr 0#5)) G.pq.cap G.pq.ptr _) ?_
                wp_done
              · wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
                  (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) % 2^64))
                refine SepWP.weaken_pre
                  (tail_dealloc_ss2_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                    _ _ (freeOnlyPool A lim st _) s0.sp _ _ _ _ _ _) ?_
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
                  (stackAt (s0.sp - 48#64) dropChainStack ∗ cells (s0.sp - 48#64) 6))
                  (by
                    rw [← tail_stack_ss2_96_from_bottom s0.sp]
                    exact Entails.of_eq (by sep_ac_rfl)) ?_
                cells_unfold
                wp_pull_exists
                wp_done

/-- `core::ptr::drop_glue::<SessionStructure> [local#4]` (`69` insns) meets
`dropSessionStructureLocal2SpecBase M A lim` on `tripleRatchetProgAtExt b ext` from `dealloc` alone. -/
theorem drop_session_structure3_of_dealloc_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2SpecBase M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp =>
    (drop_session_structure3_inner_of_dealloc_ext hdealloc_fn).mono_outcome (x, st) R s0 hpc hrun
      hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [ss2InnerSpec, dropSessionStructureLocal2SpecBase] at hpost ⊢
    have hreg :
        (memRegion x.ss 24 ∗ memRegion (x.ss + 24#64) 24 ∗ memRegion (x.ss + 48#64) 24 ∗
          memRegion (x.ss + 72#64) 24 ∗ memRegion (x.ss + 96#64) 24 ∗
          memRegion (x.ss + 120#64) 24 ∗ memRegion (x.ss + 144#64) 104 ∗
          memRegion (x.ss + 248#64) 48 ∗ memRegion (x.ss + 296#64) 32 ∗
          memRegion (x.ss + 328#64) 16) ⊢ memRegion x.ss 344 := by
      simpa only [sepConj_assoc] using session_memRegions_entails_344 x.ss
    have hpost1 : sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗
        freeOnlyPool A lim st sf ∗
        stackAt s0.sp dropSessionStructureLocal2Stack) ∗ R :=
      Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hreg))) hpost
    unfold freeOnlyPool at hpost1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨htr, hpost1⟩
    have hpost2 : sf.mem ⊨
        (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
        (memRegion x.ss 344 ∗ stackAt s0.sp dropSessionStructureLocal2Stack ∗ R) := by
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

theorem drop_session_structure3_of_allocHooks_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hDealloc : HookSat ext deallocName (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2SpecBase M A lim) :=
  drop_session_structure3_of_dealloc_ext
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext b M A lim ext hDealloc deallocName 0 (Nat.add_zero _))

/-- `core::ptr::drop_glue::<SessionStructure> [local#4]` (`69` insns) meets
`dropSessionStructureLocal2SpecBase M A lim` on `tripleRatchetProgAtExt b ext`. -/
theorem drop_session_structure3_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2SpecBase M A lim) :=
  drop_session_structure3_of_dealloc_ext hA.dealloc

theorem drop_session_structure3_ok_mem4K_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2SpecBase M A lim) :=
  drop_session_structure3_of_dealloc_ext hA.dealloc

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtBudget
