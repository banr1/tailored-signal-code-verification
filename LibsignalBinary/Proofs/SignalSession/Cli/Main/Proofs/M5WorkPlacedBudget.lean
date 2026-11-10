/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public meta import Lean
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Basic-Block / OOM Combinators for `main` Hop M5 (Block `617`)

Provides `VmPreserved`-carrying `MainMemcpyROFsPlaced`, the pool-synchronizing `m5_steps_sync_pool`
tactic, budget-threaded `handle_error` OOM panic combinators, and `A.atState` / `A.repAlloc` spatial
equivalence lemmas on Block `617`.
-/

@[expose] public section

set_option linter.dupNamespace false
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (ls_subroutine_ok_rocl_of_block withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack memcpyName withStack)
open CryptoVerification.RustHeap (allocFailedIn)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost dirAt)
open CryptoVerification.SignalSession.Cli.Main.Placed (blkPC_617 blkPl_617 lsProg_617)
open CryptoVerification.SignalSession.Cli.MainHops
  (InMainPlaced LsCodeInv M5ErrEntryPlaced allocFailedIn_of_prefix argsBuf dirsAt
   lsHandleErrorSymMain m5ErrCellsPlaced m5LoopCellsPlaced mPcPlaced mainFrameSize ownedBytes
   storesDirs)
open CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
  (m5WorkRestPlaced m5_run_placed m5_seq_placed mPcPlaced_eq_blkPl)
open scoped CryptoVerification.SignalSession.Cli.MainHops.LoopDrop
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsFsPlaced)

/-- Budget-threaded relocatable `[LibsignalPlacement]` counterpart of `MainHops.MainMemcpyROFsPlaced`
on Block `617` (`withVmPreserved sessionMemcpyRegionROSpec`), satisfied by
`MainMemcpyROFsPlaced.of_alloc`. -/
abbrev MainMemcpyROFsPlaced [LibsignalPlacement] (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_617 H) (lsρ memcpyName)
    (withLsRoCl lsmpl
      (withStack (withVmPreserved sessionMemcpyRegionROSpec) extHookStack).keepsFs)

theorem MainMemcpyROFsPlaced.of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsFsPlaced A lim H) : MainMemcpyROFsPlaced H :=
  ls_subroutine_ok_rocl_of_block (i := 617) (j := 617)
    (hA.session_memcpy_region_ro extHookStack (Nat.le_refl _) (by decide)) (by decide)

@[simp]
theorem ownedBytes_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes (A.atState lim st s) cap ptr len bs = ownedBytes A.repAlloc cap ptr len bs :=
  rfl

@[simp]
theorem argsBuf_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (cap buf : BitVec 64) (ps : List (BitVec 64 × List (BitVec 8))) :
    argsBuf (A.atState lim st s) cap buf ps = argsBuf A.repAlloc cap buf ps :=
  rfl

@[simp]
theorem dirAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (d : DirGhost) :
    dirAt (A.atState lim st s) a d = dirAt A.repAlloc a d :=
  rfl

@[simp]
theorem dirsAt_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (ds : List DirGhost) :
    dirsAt (A.atState lim st s) a ds = dirsAt A.repAlloc a ds := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp only [dirsAt, dirAt_atState_eq_repAlloc, ih]

@[simp]
theorem m5WorkRestPlaced_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost) (k : Nat) :
    m5WorkRestPlaced (A.atState lim st s) fsp outCap outPtr outLen inCap inPtr g k =
      m5WorkRestPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr g k := by
  unfold m5WorkRestPlaced
  rw [dirsAt_atState_eq_repAlloc]

@[simp]
theorem m5LoopCellsPlaced_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost) (k : Nat) :
    m5LoopCellsPlaced (A.atState lim st s) fsp outCap outPtr outLen inCap inPtr g k =
      m5LoopCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr g k := by
  unfold m5LoopCellsPlaced
  rw [dirsAt_atState_eq_repAlloc]

@[simp]
theorem m5ErrCellsPlaced_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64) (g : StoresGhost) (k : Nat) :
    m5ErrCellsPlaced (A.atState lim st s) fsp outCap outPtr outLen inCap inPtr curCap curPtr g k =
      m5ErrCellsPlaced A.repAlloc fsp outCap outPtr outLen inCap inPtr curCap curPtr g k := by
  unfold m5ErrCellsPlaced
  rw [dirsAt_atState_eq_repAlloc]

@[simp]
theorem m5ErrEntryPlaced_heap_atState_eq_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (errE : M5ErrEntryPlaced) :
    errE.heap (A.atState lim st s) = errE.heap A.repAlloc := by
  cases errE <;> rfl

namespace LoopDrop

/-- `InMainPlaced`-aware counterpart of `m5_steps` that runs `wp_steps_sync_pool` so
`A.pool lim st s` in the separation-logic precondition stays synchronized with the stepped state. -/
elab "m5_steps_sync_pool" mid:(ppSpace colGt term)? : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let (newHyps, pcNames, midStx) ← g.withContext do
    let goalTy := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let midStx ← match mid with
      | some m => pure m
      | none =>
        if goalTy.isAppOfArity ``SepWP 6 || goalTy.isAppOfArity ``SepWPp 7 then
          Lean.Elab.Term.exprToSyntax (goalTy.getArg! 1)
        else
          throwError "m5_steps_sync_pool: expected SepWP or SepWPp goal when `mid` is omitted"
    let mut newHyps : Array Lean.Meta.Hypothesis := #[]
    let mut pcNames : Array Lean.Name := #[]
    for decl in (← Lean.MonadLCtx.getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``InMainPlaced 5 then
          let pf ← Lean.Meta.mkAppM ``CryptoVerification.SignalSession.Cli.MainHops.LoopDrop.InMainPlaced.sp_aligned #[decl.toExpr]
          let hty ← Lean.Meta.inferType pf
          newHyps := newHyps.push { userName := Lean.Name.mkSimple "hspA", type := hty, value := pf }
          let pfPc ← Lean.Meta.mkAppM ``CryptoVerification.SignalSession.Cli.MainHops.LoopDrop.InMainPlaced.pc_blkPl #[decl.toExpr]
          let htyPc ← Lean.Meta.inferType pfPc
          newHyps := newHyps.push { userName := Lean.Name.mkSimple "hpcBlk", type := htyPc, value := pfPc }
        else if !decl.hasValue && ty.isAppOfArity ``Eq 3 &&
            ((ty.getArg! 2).find? (·.isConstOf ``mPcPlaced)).isSome then
          pcNames := pcNames.push decl.userName
    return (newHyps, pcNames, midStx)
  let (_, g1) ← g.assertHypotheses newHyps
  Lean.Elab.Tactic.replaceMainGoal [g1]
  for nm in pcNames do
    let id := Lean.mkIdent nm
    Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [mPcPlaced_eq_blkPl, BitVec.ofNat_eq_ofNat] at $id:ident))
  Lean.Elab.Tactic.evalTactic (← `(tactic| (try simp only [mPcPlaced_eq_blkPl, BitVec.ofNat_eq_ofNat]); wp_steps_sync_pool $midStx))

/-- Execute Loop A capacity-overflow OOM cold tail `M+0xbb0 -> M+0xbbc: bl handle_error`
(`str xzr, [sp, #0x58]; ldr x0, [sp, #0x58]; mov x1, x28; bl handle_error`). -/
theorem m5_oom_bb0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {s0 s : State} {v58 : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpanic_stub : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xbb0)
    (hP : P ⊢ ((s.sp + 0x58#64) ↦₆₄ v58) ∗ F)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_run_placed hs.inv hP (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ hpanic_stub)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  simp only [arm64_norm]
  exact List.prefix_refl _

/-- Execute Loop A alloc-null OOM cold tail `M+0xbb4 -> M+0xbbc: bl handle_error`
(`ldr x0, [sp, #0x58]; mov x1, x28; bl handle_error`). -/
theorem m5_oom_bb4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {s0 s : State} {v58 : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpanic_stub : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xbb4)
    (hP : P ⊢ ((s.sp + 0x58#64) ↦₆₄ v58) ∗ F)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_run_placed hs.inv hP (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ hpanic_stub)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  simp only [arm64_norm]
  exact List.prefix_refl _

/-- Execute Loop B capacity-overflow OOM cold tail `M+0xba4 -> M+0xbac: bl handle_error`
(`mov x0, xzr; mov x1, x23; bl handle_error`). -/
theorem m5_oom_ba4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpanic_stub : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xba4)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_seq_placed hs.inv (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ hpanic_stub)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  exact List.prefix_refl _

/-- Execute Loop B alloc-null OOM cold tail `M+0xba8 -> M+0xbac: bl handle_error`
(`mov x1, x23; bl handle_error`). -/
theorem m5_oom_ba8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {H : LibsignalHooks}
    {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpanic_stub : (lsProg_617 H).externAt? (lsρ lsHandleErrorSymMain) = some Rust.panicked)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xba8)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_seq_placed hs.inv (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ hpanic_stub)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  exact List.prefix_refl _

end LoopDrop

export LoopDrop
  (m5_oom_bb0_placed m5_oom_bb4_placed m5_oom_ba4_placed m5_oom_ba8_placed)

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5WorkPlacedBudget
