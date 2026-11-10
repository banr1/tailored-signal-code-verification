/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropChain2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2Ext
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public meta import Lean.Elab.Tactic -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.ShardFill.DropGlueChainL4
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `ext`-Parameterized `drop_chain2` on `tripleRatchetProgAtExt`

Proves `drop_proto_chain2_of_dealloc_ext`, `drop_chain2_of_dealloc_ext`, and
`drop_chain2_ok_ext` against `dropProtoChainSpec M A lim` and `dropChainSpec M A lim` on
`tripleRatchetProgAtExt b ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters hiding dropChainSpec dropProtoChainSpec
open DropGlueFacts
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs PoolPreserved
  RustCliAllocBudget VmPreserved rustDeallocEvents rustCliDeallocBudgetSpecBase
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4KBudget (
  AllocContractsMem4KBudget dealloc_ok_at_ext
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsBudget)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  dropChainSpecBase dropProtoChainSpecBase
)

attribute [local irreducible] Program.fetch Program.externAt?

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

private theorem freeOnlyPool_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s) =
      freeOnlyPool A lim st s := rfl

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

private theorem chainOuterHeadersAt_entails_memRegions (a : BitVec 64) (g : ChainGhost)
    (ckCap ckPtr : BitVec 64) :
    chainOuterHeadersAt a g ckCap ckPtr ⊢ memRegion a 48 ∗ memRegion (a + 72#64) 32 :=
  DropGlueFacts.chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr

private theorem vecAt_expose_loop_at_48 {α : Type} (A : RustAlloc) (sz align : Nat)
    (elem : α → BitVec 64 → SepProp) (a cap ptr : BitVec 64) (xs : List α) :
    vecAt A sz align elem (a + 48#64) cap ptr xs ⊢
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * sz < 2 ^ 63 ∧ xs.length * sz < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗
      ((a + 64#64) ↦₆₄ BitVec.ofNat 64 xs.length) ∗
      arrayAt elem sz ptr xs ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * sz) align ∗
         memRegion (ptr + BitVec.ofNat 64 (xs.length * sz)) ((cap.toNat - xs.length) * sz)) := by
  have h := vecAt_expose_loop A sz align elem (a + 48#64) cap ptr xs
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rwa [h1, h2] at h

private theorem post_loop_weaken_at_48 (A : RustAlloc) (a cap ptr : BitVec 64) (n : Nat)
    (hle : n ≤ cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (Rest : SepProp) :
    ((a + 48#64) ↦₆₄ cap) ∗ ((a + 56#64) ↦₆₄ ptr) ∗ ((a + 64#64) ↦₆₄ BitVec.ofNat 64 n) ∗
      memRegion ptr (n * 104) ∗
      (if cap = 0 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (n * 104)) ((cap.toNat - n) * 104)) ∗
      Rest ⊢
    ((a + 48#64) ↦₆₄ cap) ∗ (((a + 48#64) + 8#64) ↦₆₄ ptr) ∗ memRegion ((a + 48#64) + 16#64) 8 ∗
      (if cap == 0#64 then emp
       else A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104)) ∗
      Rest := by
  have h := post_loop_weaken A (a + 48#64) cap ptr n hle hcap_lt Rest
  have h1 : (a + 48#64) + 8#64 = a + 56#64 := by bv_omega
  have h2 : (a + 48#64) + 16#64 = a + 64#64 := by bv_omega
  rw [h1, h2] at h
  rw [h1, h2]
  exact h

private theorem tail_dealloc_chain_pre_weaken (v cap ptr : BitVec 64)
    (live outer pool : SepProp) (sp : BitVec 64) (fp lr x22 x21 x20 x19 : BitVec 64) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
      live ∗ outer ∗ pool ∗
      stackAt (sp - 48#64) allocHookStack ∗
      ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
      ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
      ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
    memRegion v 24 ∗ outer ∗ pool ∗
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack ∗ live := by
  have h1 := header_cells_entails_memRegion_24 v cap ptr
  have h2 :
      stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) ⊢
      memRegion (sp - 4144#64) 48 ∗ stackAt sp allocHookStack := by
    rw [tail_stack_48_from_bottom sp]
    exact sepConj_mono_right (cells6_sub48_entails sp fp lr x22 x21 x20 x19)
  have hreord :
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8 ∗
        live ∗ outer ∗ pool ∗
        stackAt (sp - 48#64) allocHookStack ∗
        ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
        ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
        ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19) =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ memRegion (v + 16#64) 8) ∗
        (live ∗ outer ∗ pool ∗
         (stackAt (sp - 48#64) allocHookStack ∗
          ((sp - 48#64) ↦₆₄ fp) ∗ ((sp - 40#64) ↦₆₄ lr) ∗
          ((sp - 32#64) ↦₆₄ x22) ∗ ((sp - 24#64) ↦₆₄ x21) ∗
          ((sp - 16#64) ↦₆₄ x20) ∗ ((sp - 8#64) ↦₆₄ x19))) := by sep_ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right h2)))) ?_
  exact Entails.of_eq (by sep_ac_rfl)

private abbrev deallocCallOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64)

private theorem drop_chain_outer_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp a : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (g : ChainGhost) (ckCap ckPtr : BitVec 64) (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 16#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x0 = a →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 84#64)
        s
        ((chainOuterHeadersAt a g ckCap ckPtr ∗
          vecPinDealloc A.repAlloc ⟨g.srk.cap, g.srk.ptr⟩ ∗
          vecPinDealloc A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
          ckDealloc A.repAlloc ckCap ckPtr) ∗
          freeOnlyPool A lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion a 48 ∗ memRegion (a + 72#64) 32) ∗
            freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro g ckCap ckPtr s Frame hpc hrun hpres hx0
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine SepWP.seq_state (mid := entry + 40#64) (P_mid := fun sm =>
    (chainOuterHeadersAt a g ckCap ckPtr ∗
      vecPinDealloc A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
      ckDealloc A.repAlloc ckCap ckPtr) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
    ?_ ?_
  · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
    by_cases hcap : (g.srk.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 40#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      wp_call hdealloc (g.srk.ptr, g.srk.cap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs g.srk.cap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1⟩
    refine SepWP.seq_state (mid := entry + 60#64) (P_mid := fun sm =>
      (chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A.repAlloc ckCap ckPtr) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a)
      ?_ ?_
    · dsimp only [chainOuterHeadersAt, vecPinDealloc, ckDealloc]
      by_cases hcap : (g.priv.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 60#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
        wp_call hdealloc (g.priv.ptr, g.priv.cap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs g.priv.cap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      have hstep3 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 84#64) s2
          ((chainOuterHeadersAt a g ckCap ckPtr ∗ ckDealloc A.repAlloc ckCap ckPtr) ∗
            freeOnlyPool A lim st s2 ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ chainOuterHeadersAt a g ckCap ckPtr ∗ freeOnlyPool A lim st sm ∗
              stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧
            sm.readReg64 .x19 = a) := by
        dsimp only [chainOuterHeadersAt, ckDealloc]
        by_cases hcap : ckCap.slt 1#64 = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 84#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
          wp_call hdealloc (ckPtr, ckCap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs ckCap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left
          (chainOuterHeadersAt_entails_memRegions a g ckCap ckPtr)), h.2⟩)

private theorem drop_chain_body_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp v ptr : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (s : State) (Frame : SepProp),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 100#64)
        s
        (messageKeyAt A.repAlloc (pin, mk) cur ∗ freeOnlyPool A lim st s ∗
          stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗ freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗
            Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 48#64) := by
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro cur cnt pin mk s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_dealloc A.repAlloc cur pin mk)) ?_
  refine SepWP.seq_state (mid := entry + 132#64) (P_mid := fun sm =>
    (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.mac ∗ vecPinDealloc A.repAlloc pin.iv ∗
      vecPinDealloc A.repAlloc pin.seed) ∗
    freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
    ?_ ?_
  · dsimp only [mkHeadersAt, vecPinDealloc]
    by_cases hcap : (pin.cipher.cap == 0#64) = true <;>
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
    · wp_steps_sync_pool (entry + 132#64)
      wp_done
    · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
      wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
        (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
      wp_call hdealloc (pin.cipher.ptr, pin.cipher.cap.toNat, 1, M.stepEvents evs st)
      have _htr_d := ‹AllocCallPreserved _ sf›.2.1
      apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pin.cipher.cap.toNat 1 sf) (by sep_focus)
      refine align_pre_state (by rw [hsp]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1⟩, hx19_1,
    hx20_1, hx21_1, hx22_1⟩
    refine SepWP.seq_state (mid := entry + 152#64) (P_mid := fun sm =>
      (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.iv ∗ vecPinDealloc A.repAlloc pin.seed) ∗
      freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
      ?_ ?_
    · dsimp only [mkHeadersAt, vecPinDealloc]
      by_cases hcap : (pin.mac.cap == 0#64) = true <;>
        simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
      · wp_steps_sync_pool (entry + 152#64)
        wp_done
      · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
        wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
        wp_call hdealloc (pin.mac.ptr, pin.mac.cap.toNat, 1, M.stepEvents evs st)
        have _htr_d := ‹AllocCallPreserved _ sf›.2.1
        apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pin.mac.cap.toNat 1 sf) (by sep_focus)
        refine align_pre_state (by rw [hsp_1]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine SepWP.seq_state (mid := entry + 172#64) (P_mid := fun sm =>
        (mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.seed) ∗
        freeOnlyPool A lim st sm ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64)
        ?_ ?_
      · dsimp only [mkHeadersAt, vecPinDealloc]
        by_cases hcap : (pin.iv.cap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (entry + 172#64)
          wp_done
        · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
          wp_call hdealloc (pin.iv.ptr, pin.iv.cap.toNat, 1, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pin.iv.cap.toNat 1 sf) (by sep_focus)
          refine align_pre_state (by rw [hsp_2]; sep_ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3⟩,
        hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext)) (entry + 100#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDealloc A.repAlloc pin.seed) ∗
              freeOnlyPool A lim st s3 ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ freeOnlyPool A lim st sm ∗
                stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          dsimp only [mkHeadersAt, vecPinDealloc]
          by_cases hcap : (pin.seed.cap == 0#64) = true <;>
            simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
          · wp_steps_sync_pool (entry + 100#64)
            wp_done
          · refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
            wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
              (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
            wp_call hdealloc (pin.seed.ptr, pin.seed.cap.toNat, 1, M.stepEvents evs st)
            have _htr_d := ‹AllocCallPreserved _ sf›.2.1
            wp_steps_sync_pool (entry + 100#64)
            apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs pin.seed.cap.toNat 1 _) (by sep_focus)
            refine align_pre_state (by rw [hsp_3]; sep_ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 (fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩)

private theorem drop_chain_loop_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + deallocCallOff)
      (rustCliDeallocBudgetSpecBase M A lim))
    (s0 : State) (fsp v ptr : BitVec 64) (st : M.σ)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 104 < 2 ^ 63 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 112#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = ptr →
      s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 48#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name + 196#64)
        s
        (arrayAt (messageKeyAt A.repAlloc) 104 cur rest ∗ freeOnlyPool A lim st s ∗
          stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗ freeOnlyPool A lim st sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = v) := by
  have hbody := drop_chain_body_ext hdealloc s0 fsp v ptr st hfsp_align
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at *
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  intro rest
  induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    rw [show arrayAt (messageKeyAt A.repAlloc) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A.repAlloc (pin, mk) cur ∗ arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine SepWP.seq_state (mid := entry + 100#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk s
        (arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩, hx19_4,
      hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps_sync_pool (entry + 196#64)
      wp_done
    | cons hd2 tl2 =>
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps_sync_pool (entry + 112#64)
      rw [sep_push_body]
      refine SepWP.mono
        (ih (cur + 104#64) _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl (by assumption)
          ⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4⟩
          hx19_4 hx20_4
          rfl
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit,
        ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

private theorem drop_chain2_dealloc_ok_at {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name +
        BitVec.ofNat 64 (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64)))
      (rustCliDeallocBudgetSpecBase M A lim) :=
  sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := deallocName)
    (spec := rustCliDeallocBudgetSpecBase M A lim)
    hdealloc_fn
    CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name
    (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
    (by fnoff_eq)

set_option maxHeartbeats 800000 in
theorem drop_proto_chain2_of_dealloc_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64} {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpecBase M A lim) := by
  simp only [dropProtoChainSpecBase]
  have hdealloc_raw := drop_chain2_dealloc_ok_at hdealloc_fn
  clear hdealloc_fn
  have hdealloc := hdealloc_raw
  simp only [rustCliDeallocBudgetSpecBase] at hdealloc
  have houter := drop_chain_outer_ext (b := b) (ext := ext) hdealloc_raw
  have hloop := drop_chain_loop_ext (b := b) (ext := ext) hdealloc_raw
  clear hdealloc_raw
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli b
    trapHooks
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")
    (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]") 252
  dsimp only [tripleRatchetProgAtExt,
    CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name,
    deallocCallOff, BitVec.ofNat_eq_ofNat] at hdealloc houter hloop ⊢
  rw [show (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" =
      (libsignalSessionCode.rebase b trapHooks).fnAddr
      "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" from rfl] at *
  generalize_entry (libsignalSessionCode.rebase b trapHooks).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" = entry
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨⟨a, g, c⟩, st⟩
  dsimp only at *
  subst h
  conv => arg 5; ext sf P_f; rw [freeOnlyPool_eq A lim st sf]
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [show dropChainStack = dropVecMessageKeyStack from rfl]
  nth_rw 1 [stackAt_dropVecMessageKey_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (protoChainAt_entails_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) g c)) ?_
  wp_pull_exists
  rename_i ckCap ckPtr
  refine SepWP.seq_state (mid := entry + 16#64)
    (P_mid := fun sm =>
      (chainOuterHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g ckCap ckPtr ∗
        vecPinDealloc A.repAlloc ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDealloc A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDealloc A.repAlloc ckCap ckPtr) ∗
      freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
        (g.keys.zip c.messageKeys) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · wp_steps_sync_pool (entry + 16#64)
    apply SepWP.fold (freeOnlyPool_intro A lim st _) (by sep_focus)
    refine align_pre_state
      (by dsimp only [chainOuterHeadersAt, Reg.x19, Reg.x20, Reg.x21,
            Reg.x22, Reg.lr, Reg.fp]; try sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 ⟨hpres1, hx0_1⟩
    refine SepWP.seq_state (mid := entry + 84#64)
      (P_mid := fun sm =>
        vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
        freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (Q := fun sm =>
        Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5))
      ?_ ?_
    · dsimp only [chainOuterHeadersAt]
      simp only [sepConj_assoc]
      refine SepWP.mono
        (houter s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align g ckCap ckPtr s1
          (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
           ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
           ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
          hpc1 hrun1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩,
      hx19_2⟩
      refine SepWP.weaken_pre
        (sepConj_mono_left (vecAt_expose_loop_at_48 A.repAlloc 104 8 (messageKeyAt A.repAlloc)
          (s0.readReg64 (Reg.gpr 0#5)) g.mkCap g.mkPtr (g.keys.zip c.messageKeys))) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      generalize g.keys.zip c.messageKeys = mks at hlen_le hlen_lt ⊢
      refine SepWP.seq_state (mid := entry + 196#64)
        (P_mid := fun sm =>
          ((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
          ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
          memRegion g.mkPtr (mks.length * 104) ∗
          (if g.mkCap = 0 then emp
           else A.repAlloc.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
             memRegion (g.mkPtr + BitVec.ofNat 64 (mks.length * 104))
               ((g.mkCap.toNat - mks.length) * 104)) ∗
          (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
          freeOnlyPool A lim st sm ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x20 = g.mkPtr)
        ?_ ?_
      · cases mks with
        | nil =>
          simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
          wp_steps_sync_pool (entry + 196#64)
          wp_done
        | cons hd tl =>
          have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
          wp_steps_sync_pool (entry + 112#64)
          refine SepWP.weaken_pre ?_
            (SepWP.mono
              (hloop s0 (s0.sp - 48#64) g.mkPtr (s0.readReg64 (Reg.gpr 0#5)) st hfsp_align
                (hd :: tl) g.mkPtr _
                (((s0.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ g.mkCap) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ g.mkPtr) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
                  (if g.mkCap = 0 then emp
                   else A.repAlloc.live g.mkPtr (g.mkCap.toNat * 104) 8 ∗
                     memRegion (g.mkPtr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                       ((g.mkCap.toNat - (hd :: tl).length) * 104)) ∗
                  (memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗
                    memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 32) ∗
                  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
                  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
                    ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
                  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
                    ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
                (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
                ⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2⟩
                hx19_2 rfl rfl rfl) ?_)
          · exact Entails.of_eq (by sep_ac_rfl)
          · intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            exact Entails.of_eq (by sep_ac_rfl)
      · intro sm hpcm hrunm ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace⟩, hx19, hx20⟩
        refine SepWP.weaken_pre
          (post_loop_weaken_at_48 A.repAlloc (s0.readReg64
            (Reg.gpr 0#5)) g.mkCap g.mkPtr mks.length hlen_le hcap_lt _) ?_
        by_cases hcap : (g.mkCap == 0#64) = true <;>
          simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj, RustCliAllocBudget.repAlloc_live]
        · wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
          refine SepWP.weaken_pre
            (DropGlueFacts.chain_cap0_weaken (s0.readReg64
              (Reg.gpr 0#5)) g.mkCap g.mkPtr (freeOnlyPool A lim st _) s0.sp _ _ _ _ _ _) ?_
          wp_done
        · wp_steps_sync_pool (entry + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")) % 2^64))
          have hmul : 104#64 * g.mkCap = BitVec.ofNat 64 (g.mkCap.toNat * 104) := by bv_omega
          refine SepWP.weaken_pre
            (tail_dealloc_chain_pre_weaken (s0.readReg64 (Reg.gpr 0#5) + 48#64) g.mkCap g.mkPtr
              _ _ (freeOnlyPool A lim st _) s0.sp _ _ _ _ _ _) ?_
          refine sepWP_open_freeOnlyPool (by sep_focus) fun evs hevs => ?_
          wp_call hdealloc (g.mkPtr, g.mkCap.toNat * 104, 8, M.stepEvents evs st)
          have _htr_d := ‹AllocCallPreserved _ sf›.2.1
          apply SepWP.fold (freeOnlyPool_dealloc_here A lim st hevs (g.mkCap.toNat * 104) 8 sf)
            (by sep_focus)
          refine SepWP.weaken_pre
            (Entails.trans (Entails.of_eq (by sep_ac_rfl))
              (DropGlueFacts.chain_tail_dealloc_post (s0.readReg64 (Reg.gpr 0#5))
                (freeOnlyPool A lim st sf) s0.sp)) ?_
          wp_done

theorem drop_proto_chain2_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpecBase M A lim) :=
  drop_proto_chain2_of_dealloc_ext hA.dealloc

theorem drop_proto_chain2_ok_mem4K_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpecBase M A lim) :=
  drop_proto_chain2_of_dealloc_ext hA.dealloc

theorem drop_chain2_of_dealloc_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc_fn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName)
      (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpecBase M A lim) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    (drop_proto_chain2_of_dealloc_ext hdealloc_fn).mono_outcome x R s0 hpc hrun ?_ hsp
      fun _ hout => hout
  refine Satisfies.mono (sepConj_mono_left ?_) hpre
  simp only [dropChainSpecBase, dropProtoChainSpecBase]
  exact sepConj_mono_right (sepConj_mono_left (chainAt_entails_protoChainAt A.repAlloc x.1.gc x.1.a))

theorem drop_proto_chain2_of_allocHooks_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext deallocName (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropProtoChainSpecBase M A lim) :=
  drop_proto_chain2_of_dealloc_ext
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext b M A lim ext hDealloc deallocName 0 (Nat.add_zero _))

theorem drop_chain2_of_allocHooks_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hDealloc : HookSat ext deallocName (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpecBase M A lim) :=
  drop_chain2_of_dealloc_ext
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext b M A lim ext hDealloc deallocName 0 (Nat.add_zero _))

theorem drop_chain2_ok_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpecBase M A lim) :=
  drop_chain2_of_dealloc_ext hA.dealloc

theorem drop_chain2_ok_mem4K_ext {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4KBudget b M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChain2Name)
      (dropChainSpecBase M A lim) :=
  drop_chain2_of_dealloc_ext hA.dealloc

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropChain2ExtBudget
