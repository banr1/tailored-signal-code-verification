/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.Fetch
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `RawVecInner::finish_grow` and `RawVec<Chain>::grow_one`

Proves relocatable `[LibsignalPlacement]` total-correctness (`onOom := ⌜False⌝`,
`onPanic := ⌜False⌝`) contracts under `AllocContractsBudgetPlaced`:
* `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`, `16,432` B) for arbitrary
  `align ≤ 2 ^ 31` and `stride`;
* `<alloc::raw_vec::RawVec<Chain>>::grow_one` (Block `43`, `stride = 104, align = 8`, `16,896` B,
  shared by `Vec<Chain>` and `Vec<MessageKey>`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded
  withLsCodeLoaded withLsCl extract_withLsCodeLoaded
  lsmpl lsρ
  lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym
  blkPC_45 blkPl_45 blkPC_43 blkPl_43
)
open CryptoVerification.RustHeap (RustAlloc LayoutOk)
open CryptoVerification.LibsignalSession (GrowGhost)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall extHookStack sessionShimSpec sessionMemcpySpec
  ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Hooks2 (subroutine_ok_withLsCodeLoaded_map' subroutine_ok_withLsCl_map')
open Proofs.libsignal.Stage1X (finishGrowStackX growOneChainStackX session2ShimSpecX lscall_of_withLsCl)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsEvents RustLayoutOk VmPreserved
  rustAllocEvents rustReallocEvents
  RustCliAllocBudget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack rustCliDeallocNoOomSpecWithStack rustCliReallocNoOomSpecWithStack
  rustCliAllocNoOomExternSpecWithStack rustCliDeallocNoOomExternSpecWithStack
  rustCliReallocNoOomExternSpecWithStack
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  IsPow2Cap4 isPow2Cap4_zero_or_ge_four vec104GrowEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  withVmPreserved AllocContractsBudgetPlaced
  rustCliAllocNoOomSpecX rustCliDeallocNoOomSpecX rustCliReallocNoOomSpecX
  rustLayoutOk_of_layoutOk
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_vmPreserved sepWP_seq_lscl_vm sepWPp_seq_lscl_vm
)

set_option maxRecDepth 2000000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff FitsEvents
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

private meta def collectAppArgsModMData : Lean.Expr → List Lean.Expr → Lean.Expr × List Lean.Expr
  | .mdata _ e, acc => collectAppArgsModMData e acc
  | .app f a, acc => collectAppArgsModMData f (a :: acc)
  | e, acc => (e, acc)

private meta def isTrapRebase (arity : Nat) (e : Lean.Expr) : Bool :=
  let (fn, args) := collectAppArgsModMData e []
  fn.isConstOf ``Arm64.Program.rebase &&
    args.length == arity &&
    match args[2]? with
    | some h =>
      h.consumeMData.isConstOf
        ``LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift.trapHooks
    | none => false

/-- Variant of `by_vm_steps_on_withSvc` resilient to post-`wp_call` `abbrev` unfolding, `MData`
differences, and `STR`/`STP` delayed metavariable assignments (`dAssignment`): reverts newly
introduced fvars on remaining goals and temporarily closes them with dummy fvars so
`instantiateMVars` expands every `dAssignment` before replacing `Program.rebase _ _ trapHooks _`
with `((P.rebase b trapHooks).withSvc noSyscalls)`. -/
syntax "by_vm_steps_withSvc " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| by_vm_steps_withSvc $tac:tacticSeq) => do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let lctx0 ← Lean.MonadLCtx.getLCtx
      let insts0 ← Lean.Meta.getLocalInstances
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``SepWP && ty.getAppNumArgs == 6 do
        throwError "by_vm_steps_withSvc: expected `SepWP ((P.rebase b trapHooks).withSvc noSyscalls) ...`, got{Lean.indentExpr ty}"
      let e2 := (ty.getArg! 0).consumeMData
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_vm_steps_withSvc: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := (e2.getArg! 0).consumeMData
      let arity := (collectAppArgsModMData e1 []).2.length
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      let mut revInfos : Array (Nat × Lean.MVarId × Lean.Expr) := #[]
      for r in rem do
        if !(← r.isAssigned) then
          let info ← r.withContext do
            let rDecl ← r.getDecl
            let mut newFVars : Array Lean.FVarId := #[]
            for d in rDecl.lctx do
              if !d.isImplementationDetail && !lctx0.contains d.fvarId then
                newFVars := newFVars.push d.fvarId
            let (reverted, rRev) ← r.revert newFVars (preserveOrder := true)
            let revTy0 ← Lean.instantiateMVars (← rRev.getType)
            let revTy := revTy0.replace fun sub =>
              if isTrapRebase arity sub then some e2 else none
            pure (reverted.size, rRev, revTy)
          revInfos := revInfos.push info
      let rec closeWithTmp (idx : Nat) (tmps : Array Lean.Expr) :
          Lean.Elab.Tactic.TacticM (Array Lean.MVarId) := do
        if h : idx < revInfos.size then
          let (_, rRev, revTy) := revInfos[idx]
          Lean.Meta.withLocalDeclD (Lean.Name.num `_vmTmp idx) revTy fun fTmp => do
            rRev.assign fTmp
            closeWithTmp (idx + 1) (tmps.push fTmp)
        else
          let prf1 ← Lean.instantiateMVars g1
          let prf2 := prf1.replace fun sub =>
            if isTrapRebase arity sub then some e2 else none
          let mut freshGoals : Array Lean.MVarId := #[]
          let mut freshExprs : Array Lean.Expr := #[]
          for (nRev, _, revTy) in revInfos do
            let gFresh ← Lean.Meta.mkFreshExprMVarAt lctx0 insts0 revTy
            freshExprs := freshExprs.push gFresh
            let (_, gReintro) ← gFresh.mvarId!.introNP nRev
            freshGoals := freshGoals.push gReintro
          let prf3 := prf2.replace fun sub =>
            match tmps.findIdx? (· == sub) with
            | some j => freshExprs[j]?
            | none => none
          g.assign prf3
          return freshGoals
      let newRem ← closeWithTmp 0 #[]
      Lean.Elab.Tactic.setGoals (newRem.toList ++ savedGoals.tail!)

macro "by_vm_steps_s " tac:tacticSeq : tactic =>
  `(tactic| (apply sepWP_rebase_vmPreserved; by_vm_steps_withSvc $tac))

macro "wp_steps_lscl_vm_s " mid:term " as " hvm:ident hcl:ident : tactic =>
  `(tactic| (
    apply sepWP_seq_lscl_vm ‹_› (mid := $mid)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident $hcl:ident))

macro "wp_steps_p_lscl_vm_s " mid:term " as " hvm:ident hcl:ident : tactic =>
  `(tactic| (
    apply sepWPp_seq_lscl_vm ‹_› (mid := $mid)
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident $hcl:ident))

theorem sepWP_ret_vmPreserved {P : Program} {b tgt : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) tgt s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post :=
  sepWP_seq_vmPreserved (mid := tgt) hwp

macro "wp_steps_to_tgt_vm_s" " as " hvm:ident : tactic =>
  `(tactic| (
    apply sepWP_ret_vmPreserved
    by_vm_steps_withSvc (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident))

/-! ## 1. `wp_call`-Ready Extern Contract Projections on `AllocContractsBudgetPlaced` -/

/-- Single-`⌜…⌝` `wp_call` form of `withVmPreserved session2ShimSpecX`. -/
def shimVmExternSpecX : Spec Unit where
  pre := fun _ s => stackAt s.sp extHookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp extHookStack

/-- Single-`⌜…⌝` `wp_call` form of `withVmPreserved (sessionMemcpySpec extHookStack)`. -/
def memcpyVmExternSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp extHookStack

theorem alloc_extern_of_budgetPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) := by
  refine subroutine_ok_withLsCl_map' (hA.alloc (callerProg := callerProg))
    fun ⟨size, align, st⟩ R s0 hpre => ⟨(size, align, st), R, hpre, fun sf hpost => ?_⟩
  dsimp only [rustCliAllocNoOomSpecX, rustCliAllocNoOomSpecWithStack,
    rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  rcases hpost with ⟨⟨hacp, hne, hal⟩, hmem⟩
  exact ⟨⟨hacp.2.1, hne, hal⟩, hmem⟩

theorem dealloc_extern_of_budgetPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)) := by
  refine subroutine_ok_withLsCl_map' (hA.dealloc (callerProg := callerProg))
    fun ⟨p, size, align, st⟩ R s0 hpre => ⟨(p, size, align, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [rustCliDeallocNoOomSpecX, rustCliDeallocNoOomSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack,
      rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, _hlay, hlr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hlr⟩, hmem⟩
  · dsimp only [rustCliDeallocNoOomSpecX, rustCliDeallocNoOomSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack,
      rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hacp, _hlive⟩, hmem⟩
    exact ⟨hacp.2.1, hmem⟩

theorem realloc_extern_of_budgetPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)) := by
  refine subroutine_ok_withLsCl_map' (hA.realloc (callerProg := callerProg))
    fun ⟨p, old, align, new, bs, st⟩ R s0 hpre =>
      ⟨(p, old, align, new, bs, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [rustCliReallocNoOomSpecX, rustCliReallocNoOomSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomSpecWithStack,
      rustCliReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _hold, hnew, hblo, hbln, hfit, hlr⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hnew, hblo, hbln, hfit, hlr⟩, hmem⟩
  · dsimp only [rustCliReallocNoOomSpecX, rustCliReallocNoOomSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliReallocNoOomSpecWithStack,
      rustCliReallocNoOomExternSpecWithStack,
      LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hacp, hne, hal⟩, hmem⟩
    exact ⟨⟨hacp.2.1, hne, hal⟩, hmem⟩

theorem shim_extern_of_budgetPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ lsRustNoAllocShimSym)
      (withLsCl lsmpl shimVmExternSpecX) := by
  refine subroutine_ok_withLsCl_map' (hA.shim (callerProg := callerProg))
    fun x R s0 hpre => ⟨x, R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withVmPreserved, session2ShimSpecX, Spec.withHookStack, sessionShimSpec,
      shimVmExternSpecX] at hpre ⊢
    rw [emp_sepConj]
    exact hpre
  · dsimp only [withVmPreserved, session2ShimSpecX, Spec.withHookStack, sessionShimSpec,
      shimVmExternSpecX] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hrest⟩
    rw [satisfies_pure_sepConj] at hrest
    rcases hrest with ⟨htr, hmem⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨htr, hvm⟩, hmem⟩

theorem memcpy_extern_of_budgetPlaced [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H)
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H] :
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl memcpyVmExternSpecX) := by
  refine subroutine_ok_withLsCl_map' (hA.session_memcpy (callerProg := callerProg))
    fun ⟨dst, src, bs⟩ R s0 hpre => ⟨(dst, src, bs), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec,
      memcpyVmExternSpecX] at hpre ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec,
      memcpyVmExternSpecX] at hpost ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hrest⟩
    rw [satisfies_pure_sepConj] at hrest
    rcases hrest with ⟨⟨hret, htr⟩, hmem⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hret, htr, hvm⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩

/-! ## 2. Arithmetic & Stack/Memory Unfolding Lemmas -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have h1 : stride.toNat < 2 ^ 128 := by omega
  have h2 : new.toNat < 2 ^ 128 := by omega
  have hcomm : stride.toNat * new.toNat = new.toNat * stride.toNat := Nat.mul_comm _ _
  have h3 : stride.toNat * new.toNat < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : stride.toNat * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem mul_stride_ne_zero {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat h] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_stride_ne_zero h0 h

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hsub : (9223372036854775808#64 - align).toNat = 2 ^ 63 - align.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · simp
    · rw [BitVec.le_def]
      change align.toNat ≤ 2 ^ 63
      omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, hsub, mul_stride_toNat (by omega)]
  omega

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + (8 + 8) by rfl, memRegion_split a 8 (8 + 8) (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_finishGrowX (sp : BitVec 64) :
    stackAt sp finishGrowStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16384 6 (by decide)

private def growPad104X (sp : BitVec 64) : SepProp :=
  memRegion (sp - 16896#64) 400

private theorem stackAt_grow_one_104_x (sp : BitVec 64) :
    stackAt sp growOneChainStackX =
      growPad104X sp ∗
      (stackAt (sp - 64#64) finishGrowStackX ∗
        (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
         ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
          ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
          ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7))) := by
  have h1 := stackAt_split_bottom sp 16496 400 (by decide)
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16432 8 (by decide)
  change stackAt sp growOneChainStackX = growPad104X sp ∗ stackAt sp 16496 at h1
  change stackAt sp 16496 = stackAt (sp - 64#64) finishGrowStackX ∗ cells (sp - 64#64) 8 at h2
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, hc8]

private theorem grow_104_new_cap_eq {cap : BitVec 64}
    (h : max (2 * cap.toNat) 4 * 104 ≤ 9223372036854775800) :
    (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := by
  have hsh : (cap <<< 1).toNat = 2 * cap.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (cap.toNat * 2) % 2 ^ 64 = 2 * cap.toNat
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases hc : (4#64).ult (cap <<< 1) = true
  · simp only [hc, ite_true, hsh]
    have hlt : 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    omega
  · simp only [hc, Bool.false_eq_true, ite_false]
    have hle : ¬ 4 < 2 * cap.toNat := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hsh] at hc
      exact hc
    change 4 = max (2 * cap.toNat) 4
    omega

/-! ## 3. `finishGrowEvents` & `finishGrowBudgetSpecX` (Block `45`) -/

/-- Events emitted by `RawVecInner::finish_grow(cap, new, align, stride)`. -/
def finishGrowEvents (cap new align stride : Nat) : List AllocEvent :=
  if cap = 0 then rustAllocEvents (new * stride) align
  else rustReallocEvents (cap * stride) (new * stride) align

@[simp]
theorem finishGrowEvents_zero (new align stride : Nat) :
    finishGrowEvents 0 new align stride = rustAllocEvents (new * stride) align := rfl

theorem finishGrowEvents_ne {cap new align stride : Nat} (h : cap ≠ 0) :
    finishGrowEvents cap new align stride = rustReallocEvents (cap * stride) (new * stride) align := by
  simp [finishGrowEvents, h]

theorem finishGrowEvents_104_eq {cap : Nat} (hcap : cap = 0 ∨ 2 ≤ cap) :
    finishGrowEvents cap (max (2 * cap) 4) 8 104 = vec104GrowEvents cap := by
  unfold finishGrowEvents vec104GrowEvents
  split
  · rename_i h0
    subst h0
    rfl
  · rename_i hne
    have hge2 : 2 ≤ cap := hcap.resolve_left hne
    have hmax : max (2 * cap) 4 = 2 * cap := by omega
    rw [hmax]

/-- Budget-threaded total-correctness (`onOom := ⌜False⌝`, `onPanic := ⌜False⌝`) contract for
`<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` (Block `45`, `finishGrowStackX = 16,432` B). -/
def finishGrowBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      x.align.toNat ≤ 2 ^ 31 ∧ LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st (finishGrowEvents x.cap.toNat x.new.toNat x.align.toNat x.stride.toNat)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStackX
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents
      (finishGrowEvents x.cap.toNat x.new.toNat x.align.toNat x.stride.toNat) st
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length)
        (x.new.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool lim st' sf ∗ stackAt s0.sp finishGrowStackX

private def finishGrowZeroBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap = 0#64 ∧ x.bs = [] ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      x.align.toNat ≤ 2 ^ 31 ∧ LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st (rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStackX
  post := (finishGrowBudgetSpecX M A lim).post

private def finishGrowNeBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrowCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
      x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      x.align.toNat ≤ 2 ^ 31 ∧ LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEvents M lim st
        (rustReallocEvents (x.cap.toNat * x.stride.toNat)
          (x.new.toNat * x.stride.toNat) x.align.toNat)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStackX
  post := (finishGrowBudgetSpecX M A lim).post

private theorem finish_grow_zero_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowZeroBudgetSpecX M A lim)) := by
  unfold withLsCodeLoaded finishGrowZeroBudgetSpecX finishGrowBudgetSpecX
  simp only [memRegion_24_cells, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init xpair s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := xpair
  dsimp only at *
  rcases ‹LayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨hsz_pos, hpow, hbound⟩
  have hal31 : align.toNat ≤ 2 ^ 31 := ‹_›
  have hfit : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := ‹_›
  subst cap
  subst bs
  rw [‹s0.readReg64 (Reg.gpr 1#5) = 0#64›]
  simp only [BitVec.toNat_zero, finishGrowEvents_zero, pointsToBytes_nil, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul := mul_stride_toNat hlt64
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    rustLayoutOk_of_layoutOk hal31 ⟨hsz_pos, hpow, hbound⟩
  wp_steps_lscl_vm_s (lsρ lsRustNoAllocShimSym) as hvm1 hcl1
  apply SepWP.transport_budgetPool hvm1
  have hshim_call := lscall_of_withLsCl
    (shim_extern_of_budgetPlaced hA (callerProg := (blkPC_45).rebase (blkPl_45).base H)) hcl1
  apply CryptoVerification.sepWP_seq_lscl (mid := lsρ lsRustAllocSym) hcl1
  wp_call hshim_call ()
  apply SepWP.transport_budgetPool ‹VmPreserved _ _›
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  have halloc_call := lscall_of_withLsCl
    (alloc_extern_of_budgetPlaced hA (callerProg := (blkPC_45).rebase (blkPl_45).base H)) hcl2
  wp_call halloc_call (new.toNat * stride.toNat, align.toNat, st)
  have hne_alloc : sf_1.readReg64 .x0 ≠ 0#64 := ‹_›
  have hne_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hne_alloc
  have hmul_bv := mul_stride_eq_ofNat hlt64
  wp_steps_to_tgt_vm_s as hvm_end
  apply SepWP.transport_budgetPool hvm_end
  apply CryptoVerification.LibsignalSession.RawVecGrowOne.SepWP.instantiate_post_exists
    (sf_1.readReg64 .x0)
  wp_done

private theorem finish_grow_ne_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowNeBudgetSpecX M A lim)) := by
  unfold withLsCodeLoaded finishGrowNeBudgetSpecX finishGrowBudgetSpecX
  simp only [memRegion_24_cells, stackAt_finishGrowX, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init xpair s0
  obtain ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩ := xpair
  dsimp only [FinishGrowCall.oldBuf] at *
  rcases ‹LayoutOk (new.toNat * stride.toNat) align.toNat› with ⟨hsz_pos, hpow, hbound⟩
  have hcap_ne : cap ≠ 0#64 := ‹_›
  have hstr_pos : 0 < stride.toNat := ‹_›
  have hcap_le_new : cap.toNat ≤ new.toNat := ‹_›
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := ‹_›
  have hal31 : align.toNat ≤ 2 ^ 31 := ‹_›
  have hfit : FitsEvents M lim st
      (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := ‹_›
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hcap_ne_nat : cap.toNat ≠ 0 := by omega
  simp only [hcap_ne, ite_false, finishGrowEvents_ne hcap_ne_nat,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm] at *
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul := mul_stride_toNat hlt64
  have hmul_cap := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hrlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    rustLayoutOk_of_layoutOk hal31 ⟨hold_pos, hpow, by omega⟩
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    rustLayoutOk_of_layoutOk hal31 ⟨hsz_pos, hpow, hbound⟩
  wp_steps_lscl_vm_s (lsρ lsRustReallocSym) as hvm1 hcl1
  apply SepWP.transport_budgetPool hvm1
  have hrealloc_call := lscall_of_withLsCl
    (realloc_extern_of_budgetPlaced hA (callerProg := (blkPC_45).rebase (blkPl_45).base H)) hcl1
  wp_call hrealloc_call (ptr, cap.toNat * stride.toNat, align.toNat,
    new.toNat * stride.toNat, bs, st)
  have hne_realloc : sf.readReg64 .x0 ≠ 0#64 := ‹_›
  have hne_beq : (sf.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hne_realloc
  have hmul_bv := mul_stride_eq_ofNat hlt64
  wp_steps_to_tgt_vm_s as hvm_end
  apply SepWP.transport_budgetPool hvm_end
  apply CryptoVerification.LibsignalSession.RawVecGrowOne.SepWP.instantiate_post_exists
    (sf.readReg64 .x0)
  wp_done

/-- Block `45` (`RawVecInner::finish_grow [local#1]`) meets `finishGrowBudgetSpecX` under
`AllocContractsBudgetPlaced`. -/
theorem finish_grow_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowBudgetSpecX M A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_zero_budget_placed_ok hA).mono_outcome (x, st) R s0 hpc hrun ?_ hsp
      fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [finishGrowBudgetSpecX, finishGrowZeroBudgetSpecX, FinishGrowCall.oldBuf,
      hcap0, BitVec.toNat_zero, finishGrowEvents_zero, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hal, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hal, hlay, hfit⟩, hmem⟩
  · have hcap_ne_nat : x.cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    refine (finish_grow_ne_budget_placed_ok hA).mono_outcome (x, st) R s0 hpc hrun ?_ hsp
      fun _ hout => hout
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl0, ?_⟩
    simp only [finishGrowBudgetSpecX, finishGrowNeBudgetSpecX, FinishGrowCall.oldBuf,
      hcap0, finishGrowEvents_ne hcap_ne_nat, ite_false,
      sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
    rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hal, hlay, hfit⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hal, hlay, hfit⟩, hmem⟩

/-- Caller-block-polymorphic `withLsCl` form of `finish_grow_budget_placed_ok`. -/
theorem finish_grow_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 45)
      (withLsCl lsmpl (finishGrowBudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_budget_placed_ok hA)

/-! ## 4. `growOne104BudgetSpecX` & Block `43` Proof (`grow_one_104_budget_placed_ok`) -/

private abbrev FG48Ghost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

private def finishGrow104ZeroBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG48Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents (new.toNat * 104) 8) st
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' (new.toNat * 104) 8 ∗ memRegion p' (new.toNat * 104) ∗
      A.pool lim st' sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private def finishGrow104NeBudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FG48Ghost × M.σ) where
  pre := fun ((out, cap, ptr, new, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, cap, _ptr, new, bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8) st
    ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live p' (new.toNat * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * 104 - bs.length) ∗
      A.pool lim st' sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

private theorem finish_grow_104_zero_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowBudgetSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104ZeroBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    fun ⟨(out, cap, ptr, new, bs, o0, o1, o2, fsp), st⟩ R s0 hpre => ?_
  simp only [finishGrow104ZeroBudgetSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap0, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp; subst hcap0; subst hbs
  let hcall : FinishGrowCall := ⟨out, 0#64, ptr, new, 8#64, 104#64, []⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowBudgetSpecX, hcall, FinishGrowCall.oldBuf, ite_true,
      BitVec.toNat_zero, finishGrowEvents_zero,
      memRegion_24_cells, emp_sepConj, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, fun _ => trivial, Nat.zero_le _, hle, hpos,
      by decide, by decide, hlay, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · simp only [finishGrowBudgetSpecX, finishGrow104ZeroBudgetSpecX, hcall,
      BitVec.toNat_zero, finishGrowEvents_zero, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepExists_sepConj_left,
      satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    change _ at hq
    rw [(rfl : (104#64 : BitVec 64).toNat = 104), (rfl : (8#64 : BitVec 64).toNat = 8)] at hq
    refine ⟨p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hp', _hal, htr⟩, hmemf⟩
    exact ⟨⟨hp', htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩

private theorem finish_grow_104_ne_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hfg : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrowBudgetSpecX M A lim))) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (withLsCodeLoaded lsmpl (finishGrow104NeBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' hfg
    fun ⟨(out, cap, ptr, new, bs, o0, o1, o2, fsp), st⟩ R s0 hpre => ?_
  simp only [finishGrow104NeBudgetSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hfsp, hcap, hbs, hle, hpos, hbound, hfit⟩, hmem⟩
  subst hfsp
  have hcap_ne_nat : cap.toNat ≠ 0 := fun hc => hcap (BitVec.eq_of_toNat_eq hc)
  let hcall : FinishGrowCall := ⟨out, cap, ptr, new, 8#64, 104#64, bs⟩
  have hlay : LayoutOk (new.toNat * (104#64 : BitVec 64).toNat) (8#64 : BitVec 64).toNat :=
    ⟨by change 0 < new.toNat * 104; omega, ⟨3, rfl⟩, by change new.toNat * 104 + 8 ≤ 2 ^ 63; omega⟩
  have hm104 : (104#64 : BitVec 64).toNat = 104 := rfl
  have ha8 : (8#64 : BitVec 64).toNat = 8 := rfl
  refine ⟨(hcall, st), R, ?_, fun sf hq => ?_⟩
  · simp only [finishGrowBudgetSpecX, hcall, FinishGrowCall.oldBuf, hcap, ite_false,
      finishGrowEvents_ne hcap_ne_nat, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live_norm,
      memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [hm104, ha8, hbs, Nat.sub_self, memRegion_zero, sepConj_emp,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, False.elim, Nat.le_refl _, hle, hpos,
      by decide, by decide, hlay, hfit⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · simp only [finishGrowBudgetSpecX, finishGrow104NeBudgetSpecX, hcall,
      finishGrowEvents_ne hcap_ne_nat, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨p', hq⟩
    rw [hm104, ha8] at hq
    refine ⟨p', BitVec.ofNat 64 (new.toNat * 104), ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨hp', _hal, htr⟩, hmemf⟩
    exact ⟨⟨hp', htr⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf⟩

theorem cap_zero_or_ge_two_of_isPow2Cap4 {cap : BitVec 64} (h : IsPow2Cap4 cap.toNat) :
    cap = 0#64 ∨ 2 ≤ cap.toNat := by
  rcases isPow2Cap4_zero_or_ge_four h with h0 | h4
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (by omega)

/-- Budget-threaded total-correctness (`onOom := ⌜False⌝`, `onPanic := ⌜False⌝`) contract for
`<alloc::raw_vec::RawVec<Chain/MessageKey>>::grow_one` (Block `43`, `stride = 104, align = 8`,
`growOneChainStackX = 16,896` B) under `FitsEvents M lim st (vec104GrowEvents cap.toNat)`. -/
def growOne104BudgetSpecX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
      (cap = 0#64 ∨ 2 ≤ cap.toNat) ∧
      max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (vec104GrowEvents cap.toNat)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
    A.pool lim st s ∗ stackAt s.sp growOneChainStackX
  post := fun ((v, cap, _, bs), st) s0 sf =>
    let st' := M.stepEvents (vec104GrowEvents cap.toNat) st
    ⌜sf.trace = s0.trace⌝ ∗
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0⌝ ∗ (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' (max (2 * cap.toNat) 4 * 104) 8 ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) ((max (2 * cap.toNat) 4 - cap.toNat) * 104) ∗
      A.pool lim st' sf ∗ stackAt s0.sp growOneChainStackX

/-- Proposition packaging `growOne104BudgetSpecX` on Block `43`. -/
def GrowOne104BudgetPlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
    (withLsCodeLoaded lsmpl (growOne104BudgetSpecX M A lim))

/-- Block `43` (`<RawVec<Chain>>::grow_one`, shared by `Vec<Chain>` and `Vec<MessageKey>`,
`stride = 104, align = 8`) meets `growOne104BudgetSpecX` with `onOom := ⌜False⌝` and
`onPanic := ⌜False⌝`. -/
theorem grow_one_104_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOne104BudgetSpecX M A lim)) := by
  simp only [withLsCodeLoaded, growOne104BudgetSpecX, stackAt_grow_one_104_x,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init xpair s0
  obtain ⟨⟨v, cap, ptr, bs⟩, st⟩ := xpair
  dsimp only at *
  have hfg := finish_grow_budget_placed_ok hA
  have hfg0_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow104ZeroBudgetSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_zero_budget_placed_ok hfg)
  have hfg1_cl : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (lsmpl.base 45)
      (withLsCl lsmpl (finishGrow104NeBudgetSpecX M A lim)) :=
    ls_subroutine_ok_cl_of_callee (j := 45) (finish_grow_104_ne_budget_placed_ok hfg)
  have hnew_eq : (if (4#64).ult (cap <<< 1) = true then cap <<< 1 else 4#64) =
      BitVec.ofNat 64 (max (2 * cap.toNat) 4) := grow_104_new_cap_eq (by omega)
  let new := BitVec.ofNat 64 (max (2 * cap.toNat) 4)
  have hnew_toNat : new.toNat = max (2 * cap.toNat) 4 := by
    dsimp [new]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by omega
  have hnew_pos : 0 < new.toNat := by omega
  have hnew_bound : new.toNat * 104 + 8 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs := List.eq_nil_of_length_eq_zero ‹bs.length = (0#64 : BitVec 64).toNat * 104›
    subst hbs
    have hnew0 : new.toNat = 4 := by
      rw [hnew_toNat, BitVec.toNat_zero]
      decide
    have hfit0 : FitsEvents M lim st (rustAllocEvents (new.toNat * 104) 8) := by
      have hf : FitsEvents M lim st (vec104GrowEvents 0) := ‹_›
      rw [hnew0]
      simpa only [vec104GrowEvents, ↓reduceIte] using hf
    simp only [BitVec.ofNat_eq_ofNat, emp_sepConj, pointsToBytes_nil, List.length_nil,
      BitVec.add_zero, BitVec.toNat_zero, Nat.mul_zero, Nat.sub_zero,
      vec104GrowEvents, ↓reduceIte]
    wp_steps_lscl_vm_s (lsmpl.base 45) as hvm1 hcl1
    apply SepWP.transport_budgetPool hvm1
    have hfg0_call := lscall_of_withLsCl hfg0_cl hcl1
    wp_call hfg0_call ((s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64), st)
    wp_steps_to_tgt_vm_s as hvm_end
    apply SepWP.transport_budgetPool hvm_end
    have hmax0 : new.toNat * 104 = 416 := by rw [hnew0]
    rw [hmax0]
    wp_done
  · have hcap0' : cap ≠ 0 := hcap0
    have hcap_ne_nat : cap.toNat ≠ 0 := fun hc => hcap0 (BitVec.eq_of_toNat_eq hc)
    have hcap_ge2 : 2 ≤ cap.toNat := (‹cap = 0#64 ∨ 2 ≤ cap.toNat›).resolve_left hcap0
    have hnew_2cap : max (2 * cap.toNat) 4 = 2 * cap.toNat := by omega
    have hfit1 : FitsEvents M lim st (rustReallocEvents (cap.toNat * 104) (new.toNat * 104) 8) := by
      have hf : FitsEvents M lim st (vec104GrowEvents cap.toNat) := ‹_›
      simpa only [vec104GrowEvents, hcap_ne_nat, ↓reduceIte, hnew_toNat, hnew_2cap] using hf
    simp only [hcap0', sepConj_assoc, vec104GrowEvents, hcap_ne_nat, ↓reduceIte]
    have hsub_mul : (max (2 * cap.toNat) 4 - cap.toNat) * 104 = new.toNat * 104 - bs.length := by
      rw [Nat.sub_mul, hnew_toNat, ‹bs.length = cap.toNat * 104›]
    rw [hsub_mul]
    wp_steps_lscl_vm_s (lsmpl.base 45) as hvm1 hcl1
    apply SepWP.transport_budgetPool hvm1
    have hfg1_call := lscall_of_withLsCl hfg1_cl hcl1
    wp_call hfg1_call ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3,
      s0.sp - 64#64), st)
    wp_steps_to_tgt_vm_s as hvm_end
    apply SepWP.transport_budgetPool hvm_end
    have h2cap_eq : new.toNat * 104 = 2 * cap.toNat * 104 := by rw [hnew_toNat, hnew_2cap]
    have hmax_mul : max (2 * cap.toNat) 4 * 104 = 2 * cap.toNat * 104 := by rw [hnew_2cap]
    rw [h2cap_eq, hmax_mul]
    wp_done

/-- Caller-block-polymorphic `withLsCl` form of `grow_one_104_budget_placed_ok`. -/
theorem grow_one_104_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 43)
      (withLsCl lsmpl (growOne104BudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 43) (grow_one_104_budget_placed_ok hA)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
