/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M5MemPlaced
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.Common

/-!
# Relocatable Scratch Lenses & Basic-Block / OOM Combinators for `main` Hop M5 (Block `617`)

Scratch-slot lenses (`m5ScratchPlaced`, `m5WorkCellsPlaced`, `m5DirPopRestPlaced`), stepping
tactics, and basic-block / `handle_error` OOM panic combinators on Block `617` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.Varint DoReserveNorm
open CryptoVerification.SignalSession.Cli.Path.Helpers

/-- Relocatable `[LibsignalPlacement]` counterpart of `MainMemcpyROFs` on Block `617`
(satisfied directly by `hA.session_memcpy_region_ro_rocl`). -/
abbrev MainMemcpyROFsPlaced [LibsignalPlacement] (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_617).rebase (blkPl_617).base H) (lsρ memcpyName)
    (withLsRoCl lsmpl
      (withStack CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec extHookStack).keepsFs)

theorem MainMemcpyROFsPlaced.of_alloc [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hA : AllocContractsFsPlaced A H) : MainMemcpyROFsPlaced H :=
  hA.session_memcpy_region_ro_rocl (prog := lsProg_617 H) (i := 617)
    extHookStack (Nat.le_refl _) (by decide)

namespace LoopDrop

theorem InMainPlaced.sp_aligned [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat} (hs : InMainPlaced CodeOk s0 s k) : s.spAligned = true := by
  simp only [State.spAligned, hs.sp, mainFrameSize]
  exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hs.spAligned

theorem InMainPlaced.pc_blkPl [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s : State} {k : Nat} (hs : InMainPlaced CodeOk s0 s k) :
    s.pc = (blkPl_617).base + BitVec.ofNat 64 k :=
  hs.pc

@[simp, arm64_norm]
theorem mPcPlaced_eq_blkPl [LibsignalPlacement] (off : Nat) :
    mPcPlaced off = (blkPl_617).base + BitVec.ofNat 64 off := rfl

private meta def hasBvTermPlaced (e : Lean.Expr) : Bool :=
  (e.find? fun sub =>
    sub.isAppOf ``BitVec.ofNat ||
      ((sub.isAppOf ``HSub.hSub || sub.isAppOf ``HAdd.hAdd || sub.isAppOf ``HMul.hMul) &&
        sub.getAppNumArgs ≥ 1 && (sub.getArg! 0).isAppOf ``BitVec)).isSome

private meta partial def isNatIntPropPlaced (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
  if hasBvTermPlaced e then false
  else if e.isConstOf ``False || e.isConstOf ``True then true
  else if let some a := e.not? then isNatIntPropPlaced a
  else if let some (a, b) := e.and? then isNatIntPropPlaced a && isNatIntPropPlaced b
  else if e.isAppOfArity ``Or 2 then isNatIntPropPlaced (e.getArg! 0) && isNatIntPropPlaced (e.getArg! 1)
  else
    let fn := e.getAppFn
    let args := e.getAppArgs
    if (fn.isConstOf ``Eq || fn.isConstOf ``Ne) && args.size == 3 then
      args[0]!.isConstOf ``Nat || args[0]!.isConstOf ``Int
    else if (fn.isConstOf ``LE.le || fn.isConstOf ``LT.lt ||
             fn.isConstOf ``GE.ge || fn.isConstOf ``GT.gt) && args.size == 4 then
      args[0]!.isConstOf ``Nat || args[0]!.isConstOf ``Int
    else false

private meta def unhideImplDetailsPlaced (g : Lean.MVarId) : Lean.MetaM Lean.MVarId :=
  g.withContext do
    let mut lctx ← Lean.MonadLCtx.getLCtx
    for decl in lctx do
      if !decl.isAuxDecl && decl.isImplementationDetail then
        lctx := lctx.setKind decl.fvarId .default
    let g' ← Lean.Meta.mkFreshExprMVarAt lctx (← Lean.Meta.getLocalInstances)
      (← g.getType) .syntheticOpaque (← g.getTag)
    g.assign g'
    return g'.mvarId!

elab "m5_prune_nat_placed" : tactic => do
  let g ← unhideImplDetailsPlaced (← Lean.Elab.Tactic.getMainGoal)
  g.withContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut toClear : Array Lean.FVarId := #[]
    for decl in lctx do
      if !decl.isAuxDecl then
        let ty ← Lean.instantiateMVars decl.type
        if decl.hasValue || !isNatIntPropPlaced ty then
          toClear := toClear.push decl.fvarId
    let g' ← g.tryClearMany toClear
    Lean.Elab.Tactic.replaceMainGoal [g']

macro (priority := high) "m5_omega" : tactic =>
  `(tactic| (m5_prune_nat_placed; try simp only [mainFrameSize, extHookStack, Nat.reducePow] at *;
             first | linarith | omega))

elab "m5_prune_bv_placed" : tactic => do
  let g0 ← Lean.Elab.Tactic.getMainGoal
  let keep ← g0.withContext do
    let mut cdecls : Array Lean.FVarId := #[]
    for decl in (← Lean.MonadLCtx.getLCtx) do
      if !decl.isImplementationDetail && !decl.hasValue then
        cdecls := cdecls.push decl.fvarId
    return if cdecls.isEmpty then none else some cdecls.back!
  let g ← unhideImplDetailsPlaced g0
  g.withContext do
    let goalTy ← Lean.instantiateMVars (← g.getType)
    let mut toClear : Array Lean.FVarId := #[]
    for decl in (← Lean.MonadLCtx.getLCtx) do
      if !decl.isAuxDecl then
        let ty ← Lean.instantiateMVars decl.type
        let isHeavy := ty.isForall ||
          (ty.find? fun s =>
            s.isConstOf ``SepWPp || s.isConstOf ``SepWP ||
            s.isConstOf ``Entails || s.isConstOf ``InMainPlaced).isSome
        let sharesGoalVar := !isHeavy && (ty.find? fun sub =>
          match sub with
          | .fvar fv => goalTy.containsFVar fv
          | _ => false).isSome
        let keepLast := some decl.fvarId == keep && sharesGoalVar
        if !keepLast && (decl.hasValue || isHeavy || !isNatIntPropPlaced ty) then
          toClear := toClear.push decl.fvarId
    let g' ← g.tryClearMany toClear
    Lean.Elab.Tactic.replaceMainGoal [g']

elab (priority := high) "m5_bv_omega" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| (
    m5_prune_bv_placed;
    try simp only [mainFrameSize, extHookStack, Nat.reducePow] at *;
    first | rfl | bv_omega)))

elab (priority := high) "m5_steps" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let (newHyps, pcNames) ← g.withContext do
    let mut newHyps : Array Lean.Meta.Hypothesis := #[]
    let mut pcNames : Array Lean.Name := #[]
    for decl in (← Lean.MonadLCtx.getLCtx) do
      if !decl.isImplementationDetail && !decl.isAuxDecl then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``InMainPlaced 5 then
          let pf ← Lean.Meta.mkAppM ``InMainPlaced.sp_aligned #[decl.toExpr]
          let hty ← Lean.Meta.inferType pf
          newHyps := newHyps.push { userName := Lean.Name.mkSimple "hspA", type := hty, value := pf }
          let pfPc ← Lean.Meta.mkAppM ``InMainPlaced.pc_blkPl #[decl.toExpr]
          let htyPc ← Lean.Meta.inferType pfPc
          newHyps := newHyps.push { userName := Lean.Name.mkSimple "hpcBlk", type := htyPc, value := pfPc }
        else if !decl.hasValue && ty.isAppOfArity ``Eq 3 &&
            ((ty.getArg! 2).find? (·.isConstOf ``mPcPlaced)).isSome then
          pcNames := pcNames.push decl.userName
    return (newHyps, pcNames)
  let (_, g1) ← g.assertHypotheses newHyps
  Lean.Elab.Tactic.replaceMainGoal [g1]
  for nm in pcNames do
    let id := Lean.mkIdent nm
    Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only [mPcPlaced_eq_blkPl, BitVec.ofNat_eq_ofNat] at $id:ident))
  Lean.Elab.Tactic.evalTactic (← `(tactic| (try simp only [mPcPlaced_eq_blkPl, BitVec.ofNat_eq_ofNat]); wp_steps))

macro "m5_steps_placed" : tactic => `(tactic| m5_steps)

/-! ## 1. Scratch-Slot & Outer-Loop Frame Lenses -/

/-- The 10 loop scratch cells inside `locals fsp`: `0x20 .. 0x50`, `0x58 .. 0x60`, and
`0x458 .. 0x470`. -/
def m5ScratchPlaced (fsp v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 : BitVec 64) : SepProp :=
  ((fsp + 0x20#64) ↦₆₄ v20) ∗ ((fsp + 0x28#64) ↦₆₄ v28) ∗ ((fsp + 0x30#64) ↦₆₄ v30) ∗
    ((fsp + 0x38#64) ↦₆₄ v38) ∗ ((fsp + 0x40#64) ↦₆₄ v40) ∗ ((fsp + 0x48#64) ↦₆₄ v48) ∗
    ((fsp + 0x58#64) ↦₆₄ v58) ∗
    ((fsp + 0x458#64) ↦₆₄ v458) ∗ ((fsp + 0x460#64) ↦₆₄ v460) ∗ ((fsp + 0x468#64) ↦₆₄ v468)

/-- Full ordered piece list with all 10 scratch slots carved around `m6CellsPlaced` + remaining `dirsAt`. -/
def m5WorkCellsPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat)
    (v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 : BitVec 64) :
    List (Nat × Nat × SepProp) :=
  [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
   cell fsp 0x20 v20, cell fsp 0x28 v28, cell fsp 0x30 v30,
   cell fsp 0x38 v38, cell fsp 0x40 v40, cell fsp 0x48 v48,
   cell fsp 0x50 inPtr, cell fsp 0x58 v58,
   (0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
     dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1))),
   cell fsp 0x458 v458, cell fsp 0x460 v460, cell fsp 0x468 v468]

/-- Invariant spatial frame of `locals fsp (m5WorkCellsPlaced …)` outside `m5ScratchPlaced`. -/
def m5WorkRestPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : SepProp :=
  ((fsp + 0x0#64) ↦₆₄ outLen) ∗ ((fsp + 0x8#64) ↦₆₄ outCap) ∗
    ((fsp + 0x10#64) ↦₆₄ inCap) ∗ ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
    ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
    memRegion (fsp + 0x60#64) ((0x1c8 + 0x28 * (k + 1)) - 0x60) ∗
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)) ∗
    memRegion (fsp + 0x308#64) (0x458 - 0x308) ∗
    memRegion (fsp + 0x470#64) (0x480 - 0x470)

theorem locals_m5WorkCellsPlaced_eq (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) {k : Nat} (hk : k < 8)
    (v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 : BitVec 64) :
    locals fsp (m5WorkCellsPlaced A fsp outCap outPtr outLen inCap inPtr g k
        v20 v28 v30 v38 v40 v48 v58 v458 v460 v468) =
      m5ScratchPlaced fsp v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 ∗
        m5WorkRestPlaced A fsp outCap outPtr outLen inCap inPtr g k := by
  have hend : (0x1c8 + 0x28 * (k + 1)) + 0x28 * (8 - (k + 1)) = 0x308 := by omega
  simp only [m5WorkCellsPlaced, m5ScratchPlaced, m5WorkRestPlaced, cell, locals, localsFrom,
    Nat.sub_self, Nat.sub_zero, Nat.reduceAdd, BitVec.add_zero, memRegion_zero, emp_sepConj, hend]
  ac_rfl

/-- Pack `m5ScratchPlaced ∗ m5WorkRestPlaced` at error exit into `locals fsp (m5ErrCellsPlaced …)`. -/
theorem m5Work_exit_to_err_placed (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr curCap curPtr : BitVec 64)
    (g : StoresGhost) {k : Nat} (hk : k < 8)
    (v40 v48 v58 v458 v460 v468 : BitVec 64) :
    m5ScratchPlaced fsp curCap curPtr (fsp + 0x1c8#64) (BitVec.ofNat 64 (k + 1))
        v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A fsp outCap outPtr outLen inCap inPtr g k ⊢
      locals fsp (m5ErrCellsPlaced A fsp outCap outPtr outLen inCap inPtr curCap curPtr g k) := by
  rw [← locals_m5WorkCellsPlaced_eq A fsp outCap outPtr outLen inCap inPtr g hk]
  let tailPiece := (0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))
  let head8 := [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr,
    cell fsp 0x20 curCap, cell fsp 0x28 curPtr, cell fsp 0x30 (fsp + 0x1c8#64),
    cell fsp 0x38 (BitVec.ofNat 64 (k + 1))]
  have h1 := locals_forget_cell fsp head8 0x40 v40
    [cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece,
     cell fsp 0x458 v458, cell fsp 0x460 v460, cell fsp 0x468 v468]
    (by simp [head8, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h2 := locals_forget_cell fsp head8 0x48 v48
    [cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece,
     cell fsp 0x458 v458, cell fsp 0x460 v460, cell fsp 0x468 v468]
    (by simp [head8, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have h3 := locals_forget_cell fsp (head8 ++ [cell fsp 0x50 inPtr]) 0x58 v58
    [tailPiece, cell fsp 0x458 v458, cell fsp 0x460 v460, cell fsp 0x468 v468]
    (by simp [head8, localsEnd])
    (by simp [tailPiece, localsBound]; omega) (by simp [tailPiece, localsBound]; omega)
  let base10 := head8 ++ [cell fsp 0x50 inPtr, tailPiece]
  have h4 := locals_forget_cell fsp base10 0x458 v458
    [cell fsp 0x460 v460, cell fsp 0x468 v468]
    (by simp [base10, head8, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  have h5 := locals_forget_cell fsp base10 0x460 v460 [cell fsp 0x468 v468]
    (by simp [base10, head8, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  have h6 := locals_forget_cell fsp base10 0x468 v468 []
    (by simp [base10, head8, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  exact Entails.trans h1 (Entails.trans h2 (Entails.trans h3 (Entails.trans h4 (Entails.trans h5 h6))))

/-- Forget all 10 scratch slots back into `locals fsp (m5LoopCellsPlaced … (k + 1))`. -/
theorem m5Work_exit_to_next_placed (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) {k : Nat} (hk : k < 8)
    (v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 : BitVec 64) :
    m5ScratchPlaced fsp v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 ∗
      m5WorkRestPlaced A fsp outCap outPtr outLen inCap inPtr g k ⊢
      locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g (k + 1)) := by
  rw [← locals_m5WorkCellsPlaced_eq A fsp outCap outPtr outLen inCap inPtr g hk]
  let tailPiece := (0x1c8 + 0x28 * (k + 1), 0x28 * (8 - (k + 1)),
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)))
  let head4 := [cell fsp 0x0 outLen, cell fsp 0x8 outCap, cell fsp 0x10 inCap, cell fsp 0x18 outPtr]
  let hi3 := [cell fsp 0x458 v458, cell fsp 0x460 v460, cell fsp 0x468 v468]
  have s1 := locals_forget_cell fsp head4 0x20 v20
    ([cell fsp 0x28 v28, cell fsp 0x30 v30, cell fsp 0x38 v38, cell fsp 0x40 v40,
      cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s2 := locals_forget_cell fsp head4 0x28 v28
    ([cell fsp 0x30 v30, cell fsp 0x38 v38, cell fsp 0x40 v40,
      cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s3 := locals_forget_cell fsp head4 0x30 v30
    ([cell fsp 0x38 v38, cell fsp 0x40 v40,
      cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s4 := locals_forget_cell fsp head4 0x38 v38
    ([cell fsp 0x40 v40, cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s5 := locals_forget_cell fsp head4 0x40 v40
    ([cell fsp 0x48 v48, cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s6 := locals_forget_cell fsp head4 0x48 v48
    ([cell fsp 0x50 inPtr, cell fsp 0x58 v58, tailPiece] ++ hi3)
    (by simp [head4, localsEnd]) (by simp [localsBound]) (by simp [localsBound])
  have s7 := locals_forget_cell fsp (head4 ++ [cell fsp 0x50 inPtr]) 0x58 v58
    ([tailPiece] ++ hi3)
    (by simp [head4, localsEnd])
    (by simp [tailPiece, localsBound]; omega) (by simp [tailPiece, localsBound]; omega)
  let base6 := head4 ++ [cell fsp 0x50 inPtr, tailPiece]
  have s8 := locals_forget_cell fsp base6 0x458 v458
    [cell fsp 0x460 v460, cell fsp 0x468 v468]
    (by simp [base6, head4, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  have s9 := locals_forget_cell fsp base6 0x460 v460 [cell fsp 0x468 v468]
    (by simp [base6, head4, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  have s10 := locals_forget_cell fsp base6 0x468 v468 []
    (by simp [base6, head4, tailPiece, localsEnd]; omega)
    (by simp [localsBound]) (by simp [localsBound])
  exact Entails.trans s1 (Entails.trans s2 (Entails.trans s3 (Entails.trans s4 (Entails.trans s5
    (Entails.trans s6 (Entails.trans s7 (Entails.trans s8 (Entails.trans s9 s10))))))))

theorem dir_slot_madd_eq (fsp : BitVec 64) (k : Nat) :
    (fsp + 0x1c8#64) + BitVec.ofNat 64 k * 0x28#64 =
      fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k) := by
  rw [BitVec.add_assoc, show (0x1c8#64 : BitVec 64) = BitVec.ofNat 64 0x1c8 from rfl,
    show (0x28#64 : BitVec 64) = BitVec.ofNat 64 0x28 from rfl,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm k 0x28]

theorem dir_slot_madd_comm (fsp : BitVec 64) (k : Nat) :
    (fsp + 0x1c8#64) + 0x28#64 * BitVec.ofNat 64 k =
      (fsp + 0x1c8#64) + BitVec.ofNat 64 k * 0x28#64 := by
  rw [BitVec.mul_comm]

theorem ubfm_lsl1_nat (v : BitVec 64) :
    BitVec.extractLsb' 0 60 (v + (v <<< (1 : Nat))) ++ 0#4 = v * 48#64 := by bv_kernel

theorem ubfm_lsl1_bv (v : BitVec 64) :
    BitVec.extractLsb' 0 60 (v + (v <<< 1#64)) ++ 0#4 = v * 48#64 := by bv_kernel

theorem shl4_lsl1_nat (v : BitVec 64) :
    ((v + (v <<< (1 : Nat))) <<< (4 : Nat)) = v * 48#64 := by bv_kernel

theorem vecBuf_pure_keep (A : RustAlloc) (curCap curPtr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) :
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr xs =
      ⌜xs.length ≤ curCap.toNat ∧ curCap.toNat * 48 < 2 ^ 63⌝ ∗
        vecBuf A 48 8 (dirEntryAt A) curCap curPtr xs := by
  apply Entails.antisymm
  · unfold vecBuf
    apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
    exact Entails.pure_right ⟨h1, h2⟩ (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _))
  · apply Entails.pure_left; intro _; exact Entails.refl _

theorem vecBuf_nil_dealloc (A : RustAlloc) (curCap curPtr : BitVec 64) :
    vecBuf A 48 8 (dirEntryAt A) curCap curPtr [] ⊢
      if curCap = 0#64 then emp
      else A.live curPtr (curCap.toNat * 48) 8 ∗ memRegion curPtr (curCap.toNat * 48) := by
  unfold vecBuf
  apply Entails.pure_left; intro _
  by_cases hc : curCap = 0
  · subst hc; simp; exact Entails.refl _
  · have hc' : curCap ≠ 0#64 := hc
    simp only [hc, hc', ↓reduceIte, arrayAt, List.length_nil, Nat.zero_mul, Nat.sub_zero,
      BitVec.add_zero, emp_sepConj]
    exact Entails.refl _

/-- Invariant spatial frame of `locals fsp (m5LoopCellsPlaced … k)` outside `dirAt A dAddr d`. -/
def m5DirPopRestPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : SepProp :=
  ((fsp + 0x0#64) ↦₆₄ outLen) ∗ ((fsp + 0x8#64) ↦₆₄ outCap) ∗
    ((fsp + 0x10#64) ↦₆₄ inCap) ∗ ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
    memRegion (fsp + 0x20#64) 0x30 ∗
    ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
    memRegion (fsp + 0x58#64) ((0x1c8 + 0x28 * k) - 0x58) ∗
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)) ∗
    memRegion (fsp + 0x308#64) (0x480 - 0x308)

theorem locals_m5LoopCellsPlaced_pop (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g k) =
      dirAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) ((storesDirs g)[k]'(by simp [hk])) ∗
        m5DirPopRestPlaced A fsp outCap outPtr outLen inCap inPtr g k := by
  have hend : (0x1c8 + 0x28 * k) + 0x28 * (8 - k) = 0x308 := by m5_omega
  simp only [m5LoopCellsPlaced, m5DirPopRestPlaced, m6CellsPlaced, cell, locals, localsFrom,
    List.cons_append, List.nil_append, Nat.sub_self, Nat.sub_zero, Nat.reduceAdd, Nat.reduceSub,
    BitVec.add_zero, memRegion_zero, emp_sepConj, sepConj_emp, Nat.mul_comm k 40,
    dirsAt_drop_cons A fsp g hk, hend]
  ac_rfl

theorem locals_m5LoopCellsPlaced_push (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28 ∗
      m5DirPopRestPlaced A fsp outCap outPtr outLen inCap inPtr g k =
    locals fsp (m5LoopCellsPlaced A fsp outCap outPtr outLen inCap inPtr g (k + 1)) := by
  rw [← locals_m5LoopCellsPlaced_step A fsp outCap outPtr outLen inCap inPtr g hk]
  have hend : (0x1c8 + 0x28 * k) + 0x28 * (8 - k) = 0x308 := by m5_omega
  simp only [m5DirPopRestPlaced, m6CellsPlaced, cell, locals, localsFrom,
    List.cons_append, List.nil_append, Nat.sub_self, Nat.sub_zero, Nat.reduceAdd, Nat.reduceSub,
    BitVec.add_zero, memRegion_zero, emp_sepConj, sepConj_emp, Nat.mul_comm k 40, hend]
  ac_rfl

/-- Mid-frame after carving the 10 scratch cells (`0x20..0x48`, `0x58`, `0x458..0x468`) out of `m5DirPopRestPlaced`. -/
def m5DirWorkMidPlaced (A : RustAlloc) (fsp outCap outPtr outLen inCap inPtr : BitVec 64)
    (g : StoresGhost) (k : Nat) : SepProp :=
  ((fsp + 0x0#64) ↦₆₄ outLen) ∗ ((fsp + 0x8#64) ↦₆₄ outCap) ∗
    ((fsp + 0x10#64) ↦₆₄ inCap) ∗ ((fsp + 0x18#64) ↦₆₄ outPtr) ∗
    ((fsp + 0x50#64) ↦₆₄ inPtr) ∗
    memRegion (fsp + 0x60#64) ((0x1c8 + 0x28 * k) - 0x60) ∗
    dirsAt A (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * (k + 1))) ((storesDirs g).drop (k + 1)) ∗
    memRegion (fsp + 0x308#64) (0x458 - 0x308) ∗
    memRegion (fsp + 0x470#64) (0x480 - 0x470)

set_option maxHeartbeats 1600000 in
theorem m5DirPopRest_carve_scratch_placed (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    m5DirPopRestPlaced A fsp outCap outPtr outLen inCap inPtr g k ⊢
      ∃∗ v20 : BitVec 64, ∃∗ v28 : BitVec 64, ∃∗ v30 : BitVec 64,
      ∃∗ v38 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v48 : BitVec 64,
      ∃∗ v58 : BitVec 64,
      ∃∗ v458 : BitVec 64, ∃∗ v460 : BitVec 64, ∃∗ v468 : BitVec 64,
        m5ScratchPlaced fsp v20 v28 v30 v38 v40 v48 v58 v458 v460 v468 ∗
          m5DirWorkMidPlaced A fsp outCap outPtr outLen inCap inPtr g k := by
  unfold m5DirPopRestPlaced
  have hlow : memRegion (fsp + 0x20#64) 0x30 = cells (fsp + 0x20#64) 6 :=
    ProofLib.memRegion_cells (fsp + 0x20#64) 6 (by decide)
  have hmid58 :
      memRegion (fsp + 0x58#64) ((0x1c8 + 0x28 * k) - 0x58) =
        cells (fsp + 0x58#64) 1 ∗ memRegion (fsp + 0x60#64) ((0x1c8 + 0x28 * k) - 0x60) := by
    have hlen58 : (0x1c8 + 0x28 * k) - 0x58 = 8 + ((0x1c8 + 0x28 * k) - 0x60) := by m5_omega
    have hsp58 := ProofLib.memRegion_split (fsp + 0x58#64) 8 ((0x1c8 + 0x28 * k) - 0x60) (by m5_omega)
    have ha58 : (fsp + 0x58#64) + BitVec.ofNat 64 8 = fsp + 0x60#64 := by m5_bv_omega
    rw [hlen58, hsp58, ha58, ProofLib.memRegion_cells (fsp + 0x58#64) 1 (by decide)]
  have hhi1 : memRegion (fsp + 0x308#64) (0x480 - 0x308) =
      memRegion (fsp + 0x308#64) (0x458 - 0x308) ∗ memRegion (fsp + 0x458#64) 40 := by
    have h1 := ProofLib.memRegion_split (fsp + 0x308#64) (0x458 - 0x308) 40 (by decide)
    have ha : (fsp + 0x308#64) + BitVec.ofNat 64 (0x458 - 0x308) = fsp + 0x458#64 := by m5_bv_omega
    rw [ha] at h1; exact h1
  have hhi2 : memRegion (fsp + 0x458#64) 40 =
      memRegion (fsp + 0x458#64) 24 ∗ memRegion (fsp + 0x470#64) (0x480 - 0x470) := by
    have h2 := ProofLib.memRegion_split (fsp + 0x458#64) 24 (0x480 - 0x470) (by decide)
    have hb : (fsp + 0x458#64) + BitVec.ofNat 64 24 = fsp + 0x470#64 := by m5_bv_omega
    rw [hb] at h2; exact h2
  rw [hlow, hmid58, hhi1, hhi2, memRegion_24_cells (fsp + 0x458#64)]
  simp only [cells_succ, cells_zero, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v468
  apply Entails.sepExists_elim; intro v460
  apply Entails.sepExists_elim; intro v458
  apply Entails.sepExists_elim; intro v58
  apply Entails.sepExists_elim; intro v20
  apply Entails.sepExists_elim; intro v28
  apply Entails.sepExists_elim; intro v30
  apply Entails.sepExists_elim; intro v38
  apply Entails.sepExists_elim; intro v40
  apply Entails.sepExists_elim; intro v48
  refine Entails.trans ?_
    (Entails.sepExists_right v20 <| Entails.sepExists_right v28 <|
      Entails.sepExists_right v30 <| Entails.sepExists_right v38 <|
      Entails.sepExists_right v40 <| Entails.sepExists_right v48 <|
      Entails.sepExists_right v58 <|
      Entails.sepExists_right v458 <| Entails.sepExists_right v460 <|
      Entails.sepExists_right v468 (Entails.refl _))
  unfold m5ScratchPlaced m5DirWorkMidPlaced
  exact Entails.of_eq (by ac_rfl)

theorem m5DirWorkMid_finish_placed (A : RustAlloc)
    (fsp outCap outPtr outLen inCap inPtr : BitVec 64) (g : StoresGhost)
    {k : Nat} (hk : k < 8) :
    memRegion (fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k)) 0x28 ∗
      m5DirWorkMidPlaced A fsp outCap outPtr outLen inCap inPtr g k =
    m5WorkRestPlaced A fsp outCap outPtr outLen inCap inPtr g k := by
  unfold m5DirWorkMidPlaced m5WorkRestPlaced
  have hlen : (0x1c8 + 0x28 * (k + 1)) - 0x60 = ((0x1c8 + 0x28 * k) - 0x60) + 0x28 := by m5_omega
  have ha : (fsp + 0x60#64) + BitVec.ofNat 64 ((0x1c8 + 0x28 * k) - 0x60) =
      fsp + BitVec.ofNat 64 (0x1c8 + 0x28 * k) := by
    rw [BitVec.add_assoc, show (0x60#64 : BitVec 64) = BitVec.ofNat 64 0x60 from rfl,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => fsp + BitVec.ofNat 64 n) (by omega)
  have hmr := ProofLib.memRegion_split (fsp + 0x60#64) ((0x1c8 + 0x28 * k) - 0x60) 0x28 (by m5_omega)
  rw [hlen, hmr, ha]
  ac_rfl

/-! ## 2. Basic-Block & OOM Panic Combinators on `mProgPlaced H` -/

theorem mkStepPlaced [LibsignalPlacement] {CodeOk : Memory → Prop}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMainPlaced CodeOk s0 s k)
    (hpc : s'.pc = (blkPl_617).base + BitVec.ofNat 64 k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hcode : CodeOk s'.mem)
    (hvregs : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InMainPlaced CodeOk s0 s' k' :=
  hs.mk_step hpc hrun hsp hfp hcode hvregs

theorem m5_seq_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hcont⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

/-- Step a basic block to `mid` on minimal footprint `P0` with arbitrary opaque frame `F`. -/
theorem m5_run_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P0 F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : CodeOk s.mem)
    (hP : P ⊢ P0 ∗ F)
    (hstep : SepWP prog mid s P0
      (fun sm Pm => sm.pc = mid → sm.status = .Running → CodeOk sm.mem →
        SepWPp prog ret sm (Pm ∗ F) Q Qp oom)
      (fun _ => ⌜False⌝)) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ P0 ∗ (F ∗ R) := by
    rw [← sepConj_assoc]; exact Satisfies.mono (sepConj_mono_left hP) hm
  rcases hstep.elim hm' hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hmm, hcont⟩ | ⟨_, hfalse⟩⟩
  · have hmm' : sm.mem ⊨ (Pm ∗ F) ∗ R := by rwa [sepConj_assoc]
    obtain ⟨sf, hsteps', hout⟩ :=
      hcont hpcm hrunm (hCI.of_keepsFrozen hinv hsteps.keepsFrozen) R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · rw [satisfies_pure_sepConj] at hfalse
    exact False.elim hfalse.1

/-- Execute Loop A capacity-overflow OOM cold tail `M+0xbb0 -> M+0xbbc: bl handle_error`
(`str xzr, [sp, #0x58]; ldr x0, [sp, #0x58]; mov x1, x28; bl handle_error`). -/
theorem m5_oom_bb0_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {s0 s : State} {v58 : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xbb0)
    (hP : P ⊢ ((s.sp + 0x58#64) ↦₆₄ v58) ∗ F)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_run_placed hs.inv hP (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ main_panic_handle_error_placed hc)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  simp only [arm64_norm]
  exact List.prefix_refl _

/-- Execute Loop A alloc-null OOM cold tail `M+0xbb4 -> M+0xbbc: bl handle_error`
(`ldr x0, [sp, #0x58]; mov x1, x28; bl handle_error`). -/
theorem m5_oom_bb4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {s0 s : State} {v58 : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xbb4)
    (hP : P ⊢ ((s.sp + 0x58#64) ↦₆₄ v58) ∗ F)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_run_placed hs.inv hP (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ main_panic_handle_error_placed hc)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  simp only [arm64_norm]
  exact List.prefix_refl _

/-- Execute Loop B capacity-overflow OOM cold tail `M+0xba4 -> M+0xbac: bl handle_error`
(`mov x0, xzr; mov x1, x23; bl handle_error`). -/
theorem m5_oom_ba4_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xba4)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_seq_placed hs.inv (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ main_panic_handle_error_placed hc)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  exact List.prefix_refl _

/-- Execute Loop B alloc-null OOM cold tail `M+0xba8 -> M+0xbac: bl handle_error`
(`mov x1, x23; bl handle_error`). -/
theorem m5_oom_ba8_placed [LibsignalPlacement] {CodeOk : Memory → Prop} [LsCodeInv CodeOk]
    {A : RustAlloc} {H : LibsignalHooks} {uuidParse : UuidParser} {hookStack resStack : Nat}
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hc : MainCalleesBlk617 A H uuidParse hookStack resStack)
    (hpanic : ∀ sf Pf, allocFailedIn s0 sf → Qp sf Pf)
    (_hs0tr : s0.trace = [])
    (hs : InMainPlaced CodeOk s0 s 0xba8)
    (haf : allocFailedIn s0 s) :
    SepWPp ((blkPC_617).rebase (blkPl_617).base H) (s0.readReg64 .lr) s P Q Qp (mainOom s0) := by
  have hpc := hs.pc
  have hrun := hs.run
  apply m5_seq_placed hs.inv (mid := lsρ lsHandleErrorSymMain)
  m5_steps
  apply SepWP.done
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
  intro hpcm hrunm _
  refine SepWPp.panic hrunm (hpcm.symm ▸ main_panic_handle_error_placed hc)
    (hpanic _ _ ?_)
  refine allocFailedIn_of_prefix haf ?_
  exact List.prefix_refl _

end LoopDrop

end CryptoVerification.SignalSession.Cli.MainHops
