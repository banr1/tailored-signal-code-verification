/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Slow
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>`

Relocatable `RustCliAllocBudget`-threaded contract and verification of
`prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (block 293).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   blkPC_261 blkPl_261 blkPC_293 blkPl_293
   lsRustAllocSym lsRustNoAllocShimSym
   ls_subroutine_ok_cl_of_plain withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (decodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack extHookStack varintSlow varintSlowAux)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (decodeVarintAux_suffix decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
  (CalleeSaved19_28 StateAt
   byte9_hi_of_ge byte9_hi_of_lt ofNat_ne_ofNat ofNat_sub_ofNat_of_le
   pointsToBytes_extract_at signExtend64_shiftLeft_63 zeroExtend64_and_127
   varintSlow_1 varintSlow_2 varintSlow_3 varintSlow_4 varintSlow_5
   varintSlow_6 varintSlow_7 varintSlow_8 varintSlow_9 varintSlow_10
   varintSlow_none_1 varintSlow_none_2 varintSlow_none_3 varintSlow_none_4
   varintSlow_none_5 varintSlow_none_6 varintSlow_none_7 varintSlow_none_8
   varintSlow_none_9 varintSlow_none_10_gt varintSlow_none_10_ovf)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost SepWPp.call_frame_lscl SepWPp.of_sepWP_lscl
   decodeErrorHookStackX
   getLsbD_7_of_gt getLsbD_7_of_le
   memRegion_48_split
   pointsTo64_pair_entails_memRegion16
   signExtend64_getLsbD_63_of_gt signExtend64_getLsbD_63_of_le
   sliceCursorAfter sliceCursorAt
   stackAt_varintSlowGen
   vAcc1 vAcc2 vAcc3 vAcc4 vAcc5 vAcc6 vAcc7 vAcc8 vAcc9 vAcc10)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowBudgetSpecWithStack decodeVarintSlowEvents
   sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromWithStack_of_decodeErrorFrom decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok decode_error_from_placed_ok_gen decode_error_from_placed_ok_x)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open Lean Elab Tactic Meta in
local elab "bind_wpp_post " qId:ident qpId:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.isAppOfArity ``SepWPp 7 do
      throwError "bind_wpp_post: expected SepWPp goal"
    let qE := ty.getArg! 4
    let qpE := ty.getArg! 5
    let g1 ← g.define qId.getId (← inferType qE) qE
    let (_, g2) ← g1.intro1P
    let g3 ← g2.withContext do g2.define qpId.getId (← inferType qpE) qpE
    let (_, g4) ← g3.intro1P
    replaceMainGoal [g4]

open Lean Elab Tactic Meta in
local elab "wp_pull_pures" : tactic => do
  let rec collectSepAtoms (fuel : Nat) (e : Expr) : Array Expr :=
    match fuel with
    | 0 => #[e]
    | fuel + 1 =>
      let e' := e.consumeMData
      if e'.isAppOfArity ``SepProp.sepConj 2 then
        collectSepAtoms fuel (e'.getArg! 0) ++ collectSepAtoms fuel (e'.getArg! 1)
      else
        #[e']
  let rec splitAndHyps (fuel : Nat) (g : MVarId) (fvars : List FVarId) : TacticM MVarId := do
    match fuel, fvars with
    | 0, _ => return g
    | _, [] => return g
    | fuel + 1, fv :: rest =>
      let ty ← g.withContext do instantiateMVars (← fv.getType)
      let ty' := ty.consumeMData
      if ty'.isAppOfArity ``And 2 then
        let a := ty'.getArg! 0
        let b := ty'.getArg! 1
        let p1 := mkApp3 (mkConst ``And.left) a b (mkFVar fv)
        let p2 := mkApp3 (mkConst ``And.right) a b (mkFVar fv)
        let n1 ← mkFreshUserName `hp
        let n2 ← mkFreshUserName `hp
        let g1 ← g.assert n1 a p1
        let (fv1, g2) ← g1.intro1P
        let g3 ← g2.assert n2 b p2
        let (fv2, g4) ← g3.intro1P
        let g5 ← g4.tryClear fv
        splitAndHyps fuel g5 (fv1 :: fv2 :: rest)
      else
        splitAndHyps fuel g rest
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    unless ty.isAppOfArity ``SepWP 6 do
      throwError "wp_pull_pures: expected SepWP goal"
    let pExpr := ty.getArg! 3
    let atoms := collectSepAtoms 200 pExpr
    let (pures, nonPures) := atoms.partition (fun a => a.isAppOfArity ``SepProp.pure 1)
    if pures.isEmpty then return
    let pRest : Expr :=
      if nonPures.isEmpty then mkConst ``SepProp.emp
      else
        let n := nonPures.size
        (List.range (n - 1)).foldr
          (fun i acc => mkApp2 (mkConst ``SepProp.sepConj) nonPures[i]! acc) nonPures[n - 1]!
    let rhs := pures.foldr (fun p acc => mkApp2 (mkConst ``SepProp.sepConj) p acc) pRest
    let progE := ty.getArg! 0
    let targetE := ty.getArg! 1
    let stateE := ty.getArg! 2
    let postE := ty.getArg! 4
    let oomE := ty.getArg! 5
    let eqTy ← mkEq pExpr rhs
    let eqPrf ← mkFreshExprMVar eqTy
    let gs ← getGoals
    setGoals [eqPrf.mvarId!]
    evalTactic (← `(tactic| sep_ac_rfl))
    setGoals gs
    let eqPrfInst ← instantiateMVars eqPrf
    let fn := mkLambda `p .default (mkConst ``SepProp)
      (mkApp6 (mkConst ``SepWP) progE targetE stateE (mkBVar 0) postE oomE)
    let goalEqPrf ← mkCongrArg fn eqPrfInst
    let newGoalTy := mkApp6 (mkConst ``SepWP) progE targetE stateE rhs postE oomE
    let g1 ← g.replaceTargetEq newGoalTy goalEqPrf
    replaceMainGoal [g1]
    let newFVars ← (List.range pures.size).foldlM (fun acc _ => do
      let hId ← mkFreshUserName `hp
      let hStx := mkIdent hId
      evalTactic (← `(tactic| (
        apply SepWP.pure_elim
        intro $hStx:ident)))
      let curG ← getMainGoal
      curG.withContext do
        match (← getLCtx).findFromUserName? hId with
        | some decl => return decl.fvarId :: acc
        | none => return acc) ([] : List FVarId)
    let curG ← getMainGoal
    let finalG ← splitAndHyps 200 curG newFVars
    replaceMainGoal [finalG]

private theorem slot8_sub_of_le (slot : BitVec 64) {n k : Nat} (hle : k ≤ n) (hn : n < 2 ^ 64) :
    ((slot + 8#64) ↦₆₄ (BitVec.ofNat 64 n - BitVec.ofNat 64 k)) =
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (n - k)) :=
  congrArg ((slot + 8#64) ↦₆₄ ·) (ofNat_sub_ofNat_of_le hle hn)

/-! ## `decodeVarintSlowSpecGen` -/

/-- Stack-parameterized budget-threaded contract of
`prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` in terms of `decodeVarint`. -/
def decodeVarintSlowSpecGen {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (errStack : Nat) : Spec (DecodeVarintSlowGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      FitsEnv M lim st (DecodeVarintSlowEnv x.bs)⌝ ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp (0x40 + errStack)
  post := fun (x, st) s0 sf =>
    (match decodeVarint x.bs with
      | some (v, _) => ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝
      | none => ⌜sf.readReg64 .x0 = 1#64⌝) ∗
      ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv x.bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (0x40 + errStack) ∗
      match decodeVarint x.bs with
      | some (_, rest) =>
        sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

abbrev decodeVarintSlowSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarintSlowSpecGen A lim decodeErrorHookStack

abbrev decodeVarintSlowSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (DecodeVarintSlowGhost × M.σ) :=
  decodeVarintSlowSpecGen A lim decodeErrorHookStackX

/-! ## Relocatable `prost::encoding::varint::decode_varint_slow::<&mut &[u8]>` (block 293) -/

set_option maxHeartbeats 3200000 in
theorem decode_varint_slow_placed_ok_with_stack [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64)
    (hFromCall : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack))) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarintSlowBudgetSpecWithStack
    simp only [stackAt_varintSlowGen herr_stk, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨slotA, slot, ptr, bs, st⟩
  dsimp only at *
  have hinv0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have h : bs.length < 2 ^ 64 := by assumption
  have hfits : FitsEnv M lim st (DecodeVarintSlowEnv bs) := by assumption
  bind_wpp_post QGoal QpGoal
  have herr : ∀ {s : State} (k : Nat),
      varintSlow bs = none →
      min 10 bs.length = k →
      StateAt s0 s ((blkPl_293).base + bv% (76)) →
      LibsignalCodeLoaded lsmpl s.mem →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (A.pool lim st s ∗
          slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        QGoal QpGoal := by
    intro s k hnone hk ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩ hinv_s
    dsimp only [QGoal, QpGoal]
    subst hk
    simp only [hnone]
    have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
      refine hfits.mono fun evs he => ?_
      simpa only [DecodeVarintSlowEnv, decodeVarintSlowEvents, hnone, DecodeErrorFromEnv] using he
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hinv_s
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
    intro hinv_call
    refine SepWPp.call_frame_lscl (pl := lsmpl)
      (spec := decodeErrorFromBudgetSpecWithStack M A lim errStack)
      (x := (s0.sp - 64#64, 0x8000000000000001#64, st))
      (φ := s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_293).base + bv% (92)) hFromCall hinv_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
      (by simp only [State.spAligned, arm64_norm, hsps]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsps]; rfl)
      ⟨rfl, by decide, hfits_de⟩
      (by sep_focus)
      (fun _ _ _ _ hex => by
        simp only [decodeErrorFromBudgetSpecWithStack] at hex
        exact not_satisfies_false_sepConj hex)
      (fun _ _ hpan => by
        simp only [decodeErrorFromBudgetSpecWithStack, sepConj_assoc] at hpan
        exact False.elim (not_satisfies_false_sepConj hpan))
      ?_
    intro sm hpcm hrunm hspm hcsm _
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromBudgetSpecWithStack, memRegion_48_split,
      sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, hsps]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro v_err
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_vs : DecodeVarintSlowEnv bs evs := by
      simpa only [DecodeVarintSlowEnv, decodeVarintSlowEvents, hnone, DecodeErrorFromEnv] using hevs_de
    have htr_sm : sm.trace = s0.trace := by
      have hp_tr : sm.trace = s.trace := by assumption
      exact hp_tr.trans htrs
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  have hok : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (52)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (A.pool lim st s ∗
          slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        QGoal QpGoal := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    dsimp only [QGoal, QpGoal]
    simp only [hsome]
    have hevs_vs : DecodeVarintSlowEnv bs [] := by
      simp only [DecodeVarintSlowEnv, decodeVarintSlowEvents, hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
    conv => arg 4; rw [hpool_nil]
    conv => arg 5; simp only [arm64_norm]
    wp_done
  have hok9 : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s ((blkPl_293).base + bv% (432)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp ((blkPC_293).rebase (blkPl_293).base H) (s0.readReg64 Reg.lr) s
        (A.pool lim st s ∗
          slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗
          stackAt (s0.sp - 64#64) errStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        QGoal QpGoal := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    dsimp only [QGoal, QpGoal]
    simp only [hsome]
    have hevs_vs : DecodeVarintSlowEnv bs [] := by
      simp only [DecodeVarintSlowEnv, decodeVarintSlowEvents, hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
    conv => arg 4; rw [hpool_nil]
    conv => arg 5; simp only [arm64_norm]
    wp_done
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (20)) hinv0
  wp_steps_sync_pool ((blkPl_293).base + bv% (20))
  simp only [State.setMem_setMem]
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  intro hinv20
  by_cases hbs0 : bs = []
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hbs0]
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv20
    wp_steps_sync_pool ((blkPl_293).base + bv% (76))
    simp only [State.setMem_setMem]
    conv => arg 4; rw [show (slot ↦₆₄ ptr) = (slot ↦₆₄ (ptr + BitVec.ofNat 64 0)) by simp,
      show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) =
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - 0)) by simp]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv76
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (herr 0 (by simp [hbs0, varintSlow, varintSlowAux]) (by simp [hbs0])
        ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
         by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
        hinv76)
  · obtain ⟨b0, bs1, hcons0'⟩ := List.exists_cons_of_ne_nil hbs0
    have hcons0 : ([] : List (BitVec 8)) ++ b0 :: bs1 = bs := hcons0'.symm
    clear hcons0' hbs0
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_ofNat (by rw [← hcons0]; simp) h (by decide)
    have hpts0 : (ptr ↦ₛ bs) = (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs1) := by
      rw [← hcons0, List.nil_append, pointsToBytes_cons]
    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (48)) hinv20
    conv => arg 4; rw [hpts0]
    wp_steps_sync_pool ((blkPl_293).base + bv% (48))
    simp only [State.setMem_setMem]
    apply SepWP.fold (Entails.of_eq hpts0.symm) (by sep_focus)
    conv => arg 4; rw [slot8_sub_of_le slot (k := 1) (by rw [← hcons0]; simp) h]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    intro hinv48
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
      wp_steps_sync_pool ((blkPl_293).base + bv% (52))
      simp only [State.setMem_setMem]
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hok (vAcc1 b0) 1 (by rw [← hcons0]; exact varintSlow_1 b0 bs1 hb0)
          ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
            by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
           by simp only [arm64_norm, vAcc1, zeroExtend64_and_127]⟩)
    · have hbit0 := getLsbD_7_of_gt hb0
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (68)) hinv48
      wp_steps_sync_pool ((blkPl_293).base + bv% (68))
      simp only [State.setMem_setMem]
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      intro hinv68
      by_cases hbs1 : bs1 = []
      · have hlen1 : BitVec.ofNat 64 bs.length = 1#64 := by rw [← hcons0, hbs1]; rfl
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv68
        wp_steps_sync_pool ((blkPl_293).base + bv% (76))
        simp only [State.setMem_setMem]
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv76
        exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (herr 1 (by rw [← hcons0, hbs1]; exact varintSlow_none_1 b0 hb0)
            (by rw [← hcons0, hbs1]; rfl)
            ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
             by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
            hinv76)
      · obtain ⟨b1, bs2, hcons1'⟩ := List.exists_cons_of_ne_nil hbs1
        have hcons1 : [b0] ++ b1 :: bs2 = bs := by rw [← hcons0, hcons1']; rfl
        clear hcons1' hbs1 hcons0
        have hlen_ne1 : BitVec.ofNat 64 bs.length ≠ 1#64 :=
          ofNat_ne_ofNat (by rw [← hcons1]; simp) h (by decide)
        have hpts1 := pointsToBytes_extract_at ptr bs [b0] bs2 b1 1 hcons1 rfl
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (136)) hinv68
        conv => arg 4; rw [hpts1]
        wp_steps_sync_pool ((blkPl_293).base + bv% (136))
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq hpts1.symm) (by sep_focus)
        conv => arg 4; rw [slot8_sub_of_le slot (k := 2) (by rw [← hcons1]; simp) h]
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        intro hinv136
        by_cases hb1 : b1 ≤ 0x7f#8
        · have hbit1 := getLsbD_7_of_le hb1
          apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
          wp_steps_sync_pool ((blkPl_293).base + bv% (52))
          simp only [State.setMem_setMem]
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (hok (vAcc2 b0 b1) 2 (by rw [← hcons1]; exact varintSlow_2 b0 b1 bs2 hb0 hb1)
              ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
               by simp only [arm64_norm, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
        · have hbit1 := getLsbD_7_of_gt hb1
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (140)) hinv136
          wp_steps_sync_pool ((blkPl_293).base + bv% (140))
          simp only [State.setMem_setMem]
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          intro hinv140
          by_cases hbs2 : bs2 = []
          · have hlen2 : BitVec.ofNat 64 bs.length = 2#64 := by rw [← hcons1, hbs2]; rfl
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv140
            wp_steps_sync_pool ((blkPl_293).base + bv% (76))
            simp only [State.setMem_setMem]
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv76
            exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
              (herr 2 (by rw [← hcons1, hbs2]; exact varintSlow_none_2 b0 b1 hb0 hb1)
                (by rw [← hcons1, hbs2]; rfl)
                ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                 by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                hinv76)
          · obtain ⟨b2, bs3, hcons2'⟩ := List.exists_cons_of_ne_nil hbs2
            have hcons2 : [b0, b1] ++ b2 :: bs3 = bs := by rw [← hcons1, hcons2']; rfl
            clear hcons2' hbs2 hcons1
            have hlen_ne2 : BitVec.ofNat 64 bs.length ≠ 2#64 :=
              ofNat_ne_ofNat (by rw [← hcons2]; simp) h (by decide)
            have hpts2 := pointsToBytes_extract_at ptr bs [b0, b1] bs3 b2 2 hcons2 rfl
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (172)) hinv140
            conv => arg 4; rw [hpts2]
            wp_steps_sync_pool ((blkPl_293).base + bv% (172))
            simp only [State.setMem_setMem]
            apply SepWP.fold (Entails.of_eq hpts2.symm) (by sep_focus)
            conv => arg 4; rw [slot8_sub_of_le slot (k := 3) (by rw [← hcons2]; simp) h]
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            intro hinv172
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := getLsbD_7_of_le hb2
              apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
              wp_steps_sync_pool ((blkPl_293).base + bv% (52))
              simp only [State.setMem_setMem]
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                (hok (vAcc3 b0 b1 b2) 3
                  (by rw [← hcons2]; exact varintSlow_3 b0 b1 b2 bs3 hb0 hb1 hb2)
                  ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                    by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                   by simp only [arm64_norm, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
            · have hbit2 := getLsbD_7_of_gt hb2
              apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (176)) hinv172
              wp_steps_sync_pool ((blkPl_293).base + bv% (176))
              simp only [State.setMem_setMem]
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              intro hinv176
              by_cases hbs3 : bs3 = []
              · have hlen3 : BitVec.ofNat 64 bs.length = 3#64 := by rw [← hcons2, hbs3]; rfl
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv176
                wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                simp only [State.setMem_setMem]
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv76
                exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                  (herr 3 (by rw [← hcons2, hbs3]; exact varintSlow_none_3 b0 b1 b2 hb0 hb1 hb2)
                    (by rw [← hcons2, hbs3]; rfl)
                    ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                     by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                    hinv76)
              · obtain ⟨b3, bs4, hcons3'⟩ := List.exists_cons_of_ne_nil hbs3
                have hcons3 : [b0, b1, b2] ++ b3 :: bs4 = bs := by rw [← hcons2, hcons3']; rfl
                clear hcons3' hbs3 hcons2
                have hlen_ne3 : BitVec.ofNat 64 bs.length ≠ 3#64 :=
                  ofNat_ne_ofNat (by rw [← hcons3]; simp) h (by decide)
                have hpts3 := pointsToBytes_extract_at ptr bs [b0, b1, b2] bs4 b3 3 hcons3 rfl
                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (208)) hinv176
                conv => arg 4; rw [hpts3]
                wp_steps_sync_pool ((blkPl_293).base + bv% (208))
                simp only [State.setMem_setMem]
                apply SepWP.fold (Entails.of_eq hpts3.symm) (by sep_focus)
                conv => arg 4; rw [slot8_sub_of_le slot (k := 4) (by rw [← hcons3]; simp) h]
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                intro hinv208
                by_cases hb3 : b3 ≤ 0x7f#8
                · have hbit3 := getLsbD_7_of_le hb3
                  apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                  wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                  simp only [State.setMem_setMem]
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                    (hok (vAcc4 b0 b1 b2 b3) 4
                      (by rw [← hcons3]; exact varintSlow_4 b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3)
                      ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                        by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                       by simp only [arm64_norm, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                · have hbit3 := getLsbD_7_of_gt hb3
                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (212)) hinv208
                  wp_steps_sync_pool ((blkPl_293).base + bv% (212))
                  simp only [State.setMem_setMem]
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  intro hinv212
                  by_cases hbs4 : bs4 = []
                  · have hlen4 : BitVec.ofNat 64 bs.length = 4#64 := by rw [← hcons3, hbs4]; rfl
                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv212
                    wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                    simp only [State.setMem_setMem]
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv76
                    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                      (herr 4
                        (by rw [← hcons3, hbs4]; exact varintSlow_none_4 b0 b1 b2 b3 hb0 hb1 hb2 hb3)
                        (by rw [← hcons3, hbs4]; rfl)
                        ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                         by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                        hinv76)
                  · obtain ⟨b4, bs5, hcons4'⟩ := List.exists_cons_of_ne_nil hbs4
                    have hcons4 : [b0, b1, b2, b3] ++ b4 :: bs5 = bs := by rw [← hcons3, hcons4']; rfl
                    clear hcons4' hbs4 hcons3
                    have hlen_ne4 : BitVec.ofNat 64 bs.length ≠ 4#64 :=
                      ofNat_ne_ofNat (by rw [← hcons4]; simp) h (by decide)
                    have hpts4 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3] bs5 b4 4 hcons4 rfl
                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (244)) hinv212
                    conv => arg 4; rw [hpts4]
                    wp_steps_sync_pool ((blkPl_293).base + bv% (244))
                    simp only [State.setMem_setMem]
                    apply SepWP.fold (Entails.of_eq hpts4.symm) (by sep_focus)
                    conv => arg 4; rw [slot8_sub_of_le slot (k := 5) (by rw [← hcons4]; simp) h]
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    intro hinv244
                    by_cases hb4 : b4 ≤ 0x7f#8
                    · have hbit4 := getLsbD_7_of_le hb4
                      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                      wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                      simp only [State.setMem_setMem]
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                        (hok (vAcc5 b0 b1 b2 b3 b4) 5
                          (by rw [← hcons4]; exact varintSlow_5 b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4)
                          ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                            by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                           by simp only [arm64_norm, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                    · have hbit4 := getLsbD_7_of_gt hb4
                      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (248)) hinv244
                      wp_steps_sync_pool ((blkPl_293).base + bv% (248))
                      simp only [State.setMem_setMem]
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      intro hinv248
                      by_cases hbs5 : bs5 = []
                      · have hlen5 : BitVec.ofNat 64 bs.length = 5#64 := by rw [← hcons4, hbs5]; rfl
                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv248
                        wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                        simp only [State.setMem_setMem]
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv76
                        exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                          (herr 5
                            (by rw [← hcons4, hbs5]; exact varintSlow_none_5 b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3 hb4)
                            (by rw [← hcons4, hbs5]; rfl)
                            ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                             by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                            hinv76)
                      · obtain ⟨b5, bs6, hcons5'⟩ := List.exists_cons_of_ne_nil hbs5
                        have hcons5 : [b0, b1, b2, b3, b4] ++ b5 :: bs6 = bs := by rw [← hcons4, hcons5']; rfl
                        clear hcons5' hbs5 hcons4
                        have hlen_ne5 : BitVec.ofNat 64 bs.length ≠ 5#64 :=
                          ofNat_ne_ofNat (by rw [← hcons5]; simp) h (by decide)
                        have hpts5 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4] bs6 b5 5 hcons5 rfl
                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (280)) hinv248
                        conv => arg 4; rw [hpts5]
                        wp_steps_sync_pool ((blkPl_293).base + bv% (280))
                        simp only [State.setMem_setMem]
                        apply SepWP.fold (Entails.of_eq hpts5.symm) (by sep_focus)
                        conv => arg 4; rw [slot8_sub_of_le slot (k := 6) (by rw [← hcons5]; simp) h]
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        intro hinv280
                        by_cases hb5 : b5 ≤ 0x7f#8
                        · have hbit5 := getLsbD_7_of_le hb5
                          apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                          wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                          simp only [State.setMem_setMem]
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                            (hok (vAcc6 b0 b1 b2 b3 b4 b5) 6
                              (by rw [← hcons5]; exact varintSlow_6 b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5)
                              ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                               by simp only [arm64_norm, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                        · have hbit5 := getLsbD_7_of_gt hb5
                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (284)) hinv280
                          wp_steps_sync_pool ((blkPl_293).base + bv% (284))
                          simp only [State.setMem_setMem]
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          intro hinv284
                          by_cases hbs6 : bs6 = []
                          · have hlen6 : BitVec.ofNat 64 bs.length = 6#64 := by rw [← hcons5, hbs6]; rfl
                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv284
                            wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                            simp only [State.setMem_setMem]
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv76
                            exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                              (herr 6
                                (by rw [← hcons5, hbs6]; exact varintSlow_none_6 b0 b1 b2 b3 b4 b5 hb0 hb1 hb2 hb3 hb4 hb5)
                                (by rw [← hcons5, hbs6]; rfl)
                                ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                 by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                hinv76)
                          · obtain ⟨b6, bs7, hcons6'⟩ := List.exists_cons_of_ne_nil hbs6
                            have hcons6 : [b0, b1, b2, b3, b4, b5] ++ b6 :: bs7 = bs := by rw [← hcons5, hcons6']; rfl
                            clear hcons6' hbs6 hcons5
                            have hlen_ne6 : BitVec.ofNat 64 bs.length ≠ 6#64 :=
                              ofNat_ne_ofNat (by rw [← hcons6]; simp) h (by decide)
                            have hpts6 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5] bs7 b6 6 hcons6 rfl
                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (316)) hinv284
                            conv => arg 4; rw [hpts6]
                            wp_steps_sync_pool ((blkPl_293).base + bv% (316))
                            simp only [State.setMem_setMem]
                            apply SepWP.fold (Entails.of_eq hpts6.symm) (by sep_focus)
                            conv => arg 4; rw [slot8_sub_of_le slot (k := 7) (by rw [← hcons6]; simp) h]
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            intro hinv316
                            by_cases hb6 : b6 ≤ 0x7f#8
                            · have hbit6 := getLsbD_7_of_le hb6
                              apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                              wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                              simp only [State.setMem_setMem]
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                (hok (vAcc7 b0 b1 b2 b3 b4 b5 b6) 7
                                  (by rw [← hcons6]; exact varintSlow_7 b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                                  ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                    by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                   by simp only [arm64_norm, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                            · have hbit6 := getLsbD_7_of_gt hb6
                              apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (320)) hinv316
                              wp_steps_sync_pool ((blkPl_293).base + bv% (320))
                              simp only [State.setMem_setMem]
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              intro hinv320
                              by_cases hbs7 : bs7 = []
                              · have hlen7 : BitVec.ofNat 64 bs.length = 7#64 := by rw [← hcons6, hbs7]; rfl
                                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv320
                                wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                                simp only [State.setMem_setMem]
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv76
                                exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                  (herr 7
                                    (by rw [← hcons6, hbs7]; exact varintSlow_none_7 b0 b1 b2 b3 b4 b5 b6 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                                    (by rw [← hcons6, hbs7]; rfl)
                                    ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                     by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                    hinv76)
                              · obtain ⟨b7, bs8, hcons7'⟩ := List.exists_cons_of_ne_nil hbs7
                                have hcons7 : [b0, b1, b2, b3, b4, b5, b6] ++ b7 :: bs8 = bs := by rw [← hcons6, hcons7']; rfl
                                clear hcons7' hbs7 hcons6
                                have hlen_ne7 : BitVec.ofNat 64 bs.length ≠ 7#64 :=
                                  ofNat_ne_ofNat (by rw [← hcons7]; simp) h (by decide)
                                have hpts7 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6] bs8 b7 7 hcons7 rfl
                                apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (352)) hinv320
                                conv => arg 4; rw [hpts7]
                                wp_steps_sync_pool ((blkPl_293).base + bv% (352))
                                simp only [State.setMem_setMem]
                                apply SepWP.fold (Entails.of_eq hpts7.symm) (by sep_focus)
                                conv => arg 4; rw [slot8_sub_of_le slot (k := 8) (by rw [← hcons7]; simp) h]
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                intro hinv352
                                by_cases hb7 : b7 ≤ 0x7f#8
                                · have hbit7 := getLsbD_7_of_le hb7
                                  apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                                  wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                                  simp only [State.setMem_setMem]
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                    (hok (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) 8
                                      (by rw [← hcons7]; exact varintSlow_8 b0 b1 b2 b3 b4 b5 b6 b7 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                      ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                        by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                       by simp only [arm64_norm, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                                · have hbit7 := getLsbD_7_of_gt hb7
                                  apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (356)) hinv352
                                  wp_steps_sync_pool ((blkPl_293).base + bv% (356))
                                  simp only [State.setMem_setMem]
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  intro hinv356
                                  by_cases hbs8 : bs8 = []
                                  · have hlen8 : BitVec.ofNat 64 bs.length = 8#64 := by rw [← hcons7, hbs8]; rfl
                                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv356
                                    wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                                    simp only [State.setMem_setMem]
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv76
                                    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                      (herr 8
                                        (by rw [← hcons7, hbs8]; exact varintSlow_none_8 b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                        (by rw [← hcons7, hbs8]; rfl)
                                        ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                         by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                        hinv76)
                                  · obtain ⟨b8, bs9, hcons8'⟩ := List.exists_cons_of_ne_nil hbs8
                                    have hcons8 : [b0, b1, b2, b3, b4, b5, b6, b7] ++ b8 :: bs9 = bs := by rw [← hcons7, hcons8']; rfl
                                    clear hcons8' hbs8 hcons7
                                    have hlen_ne8 : BitVec.ofNat 64 bs.length ≠ 8#64 :=
                                      ofNat_ne_ofNat (by rw [← hcons8]; simp) h (by decide)
                                    have hpts8 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7] bs9 b8 8 hcons8 rfl
                                    apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (388)) hinv356
                                    conv => arg 4; rw [hpts8]
                                    wp_steps_sync_pool ((blkPl_293).base + bv% (388))
                                    simp only [State.setMem_setMem]
                                    apply SepWP.fold (Entails.of_eq hpts8.symm) (by sep_focus)
                                    conv => arg 4; rw [slot8_sub_of_le slot (k := 9) (by rw [← hcons8]; simp) h]
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    intro hinv388
                                    by_cases hb8 : b8 ≤ 0x7f#8
                                    · have hbit8 := getLsbD_7_of_le hb8
                                      apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (52))
                                      wp_steps_sync_pool ((blkPl_293).base + bv% (52))
                                      simp only [State.setMem_setMem]
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                        (hok (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) 9
                                          (by rw [← hcons8]; exact varintSlow_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                          ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                            by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                           by simp only [arm64_norm, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127]⟩)
                                    · have hbit8 := getLsbD_7_of_gt hb8
                                      apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (392)) hinv388
                                      wp_steps_sync_pool ((blkPl_293).base + bv% (392))
                                      simp only [State.setMem_setMem]
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      intro hinv392
                                      by_cases hbs9 : bs9 = []
                                      · have hlen9 : BitVec.ofNat 64 bs.length = 9#64 := by rw [← hcons8, hbs9]; rfl
                                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv392
                                        wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                                        simp only [State.setMem_setMem]
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv76
                                        exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                          (herr 9
                                            (by rw [← hcons8, hbs9]; exact varintSlow_none_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                            (by rw [← hcons8, hbs9]; rfl)
                                            ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                             by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                            hinv76)
                                      · obtain ⟨b9, bs10, hcons9'⟩ := List.exists_cons_of_ne_nil hbs9
                                        have hcons9 : [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ b9 :: bs10 = bs := by rw [← hcons8, hcons9']; rfl
                                        clear hcons9' hbs9 hcons8
                                        have hlen_ne9 : BitVec.ofNat 64 bs.length ≠ 9#64 :=
                                          ofNat_ne_ofNat (by rw [← hcons9]; simp) h (by decide)
                                        have hpts9 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7, b8] bs10 b9 9 hcons9 rfl
                                        apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (416)) hinv392
                                        conv => arg 4; rw [hpts9]
                                        wp_steps_sync_pool ((blkPl_293).base + bv% (416))
                                        simp only [State.setMem_setMem]
                                        apply SepWP.fold (Entails.of_eq hpts9.symm) (by sep_focus)
                                        conv => arg 4; rw [slot8_sub_of_le slot (k := 10) (by rw [← hcons9]; simp) h]
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        intro hinv416
                                        by_cases hb9 : b9 ≤ 0x7f#8
                                        · have hbit9 := signExtend64_getLsbD_63_of_le hb9
                                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (424)) hinv416
                                          wp_steps_sync_pool ((blkPl_293).base + bv% (424))
                                          simp only [State.setMem_setMem]
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv424
                                          by_cases hb9_ovf : 2#8 ≤ b9
                                          · have hovf := byte9_hi_of_ge hb9_ovf
                                            apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv424
                                            wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                                            simp only [State.setMem_setMem]
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            intro hinv76
                                            exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                              (herr 10
                                                (by rw [← hcons9]; exact varintSlow_none_10_ovf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                                (by rw [← hcons9]; simp)
                                                ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                                 by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                                hinv76)
                                          · have hovf := byte9_hi_of_lt hb9 hb9_ovf
                                            apply SepWPp.of_sepWP (mid := (blkPl_293).base + bv% (432))
                                            wp_steps_sync_pool ((blkPl_293).base + bv% (432))
                                            simp only [State.setMem_setMem]
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                              (hok9 (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 10
                                                (by rw [← hcons9]; exact varintSlow_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                                ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                                  by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                                 by simp only [arm64_norm, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1, zeroExtend64_and_127, signExtend64_shiftLeft_63]⟩)
                                        · have hbit9 := signExtend64_getLsbD_63_of_gt hb9
                                          apply SepWPp.of_sepWP_lscl (mid := (blkPl_293).base + bv% (76)) hinv416
                                          wp_steps_sync_pool ((blkPl_293).base + bv% (76))
                                          simp only [State.setMem_setMem]
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          intro hinv76
                                          exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
                                            (herr 10
                                              (by rw [← hcons9]; exact varintSlow_none_10_gt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9)
                                              (by rw [← hcons9]; simp)
                                              ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun], by simp only [arm64_norm],
                                               by simp only [arm64_norm], by simp only [CalleeSaved19_28, arm64_norm]⟩
                                              hinv76)

/-! ## Corollaries for `decode_varint_slow` -/

theorem decode_varint_slow_placed_ok_with_stack_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim errStack)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack))) :=
  decode_varint_slow_placed_ok_with_stack herr_stk
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_293).rebase (blkPl_293).base H) hFrom)

theorem decode_varint_slow_placed_ok_with_stack_of_hooks [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hle : decodeErrorHookStack ≤ errStack := by decide)
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack))) :=
  decode_varint_slow_placed_ok_with_stack_of_contract herr_stk
    (decode_error_from_placed_ok_gen hshim halloc hle (by omega))

theorem decode_varint_slow_placed_ok_with_stack_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl
        (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))) :=
  decode_varint_slow_placed_ok_with_stack_of_hooks (errStack := 2 * extHookStack) hshim halloc

theorem decodeVarintSlowGen_lscl_ok_of_session2 {pl : Obj.MultiPlacement}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {errStack : Nat}
    (hSlow : subroutine_ok prog entry
      (withLsCodeLoaded pl
        (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack)))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (decodeVarintSlowSpecGen A lim errStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨y, st⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded pl (decodeVarintSlowBudgetSpecWithStack M A lim (0x40 + errStack))).pre
        (y.bufRef, y.slot, y.ptr, y.bs, st) s0 ∗ R := by
    simp only [withLsCodeLoaded, decodeVarintSlowSpecGen, decodeVarintSlowBudgetSpecWithStack,
      sliceCursorAt, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hr0, hlen, hfits⟩, hmem⟩
    have hmem' : s0.mem ⊨
        (y.bufRef ↦₆₄ y.slot) ∗ (y.slot ↦₆₄ y.ptr) ∗
          ((y.slot + 8#64) ↦₆₄ BitVec.ofNat 64 y.bs.length) ∗ (y.ptr ↦ₛ y.bs) ∗
          A.pool lim st s0 ∗ stackAt s0.sp (0x40 + errStack) ∗
          (⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    exact ⟨⟨hr0, by omega, hfits⟩,
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'⟩
  refine hSlow.mono_outcome (y.bufRef, y.slot, y.ptr, y.bs, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    have hvs : varintSlow y.bs =
        (decodeVarint y.bs).map (fun p => (p.1, y.bs.length - p.2.length)) :=
      decodeVarint_eq_varintSlow y.bs
    dsimp only [withLsCodeLoaded, decodeVarintSlowBudgetSpecWithStack,
      decodeVarintSlowSpecGen] at hpost ⊢
    rw [hvs] at hpost
    cases hd : decodeVarint y.bs with
    | some p =>
      rcases p with ⟨v, rest⟩
      rw [hd] at hpost
      dsimp only [Option.map, sliceCursorAfter] at hpost ⊢
      obtain ⟨k, _, _, hrest_eq⟩ := decodeVarintAux_suffix y.bs 0 0#64 v rest hd
      have hlen_sub : y.bs.length - (y.bs.length - rest.length) = rest.length := by
        rw [hrest_eq, List.length_drop]; omega
      rw [hlen_sub] at hpost
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    | none =>
      rw [hd] at hpost
      dsimp only [Option.map] at hpost ⊢
      have hpost1 : sf.mem ⊨
          ((y.slot ↦₆₄ (y.ptr + BitVec.ofNat 64 (min 10 y.bs.length))) ∗
            ((y.slot + 8#64) ↦₆₄ BitVec.ofNat 64 (y.bs.length - min 10 y.bs.length))) ∗
          (⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
            ⌜sf.trace = s0.trace⌝ ∗
            (y.bufRef ↦₆₄ y.slot) ∗
            (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv y.bs evs⌝ ∗
              A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
      have hmem1 := Satisfies.mono
        (sepConj_mono_left (pointsTo64_pair_entails_memRegion16 y.slot _ _)) hpost1
      have hmem2 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗
            (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv y.bs evs⌝ ∗
              A.pool lim (M.stepEvents evs st) sf) ∗
            stackAt s0.sp (0x40 + errStack) ∗
            decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
            memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem1
      rw [satisfies_pure_sepConj] at hmem2
      rcases hmem2 with ⟨⟨hx0, hx1⟩, hmem3⟩
      have hmem4 : sf.mem ⊨
          ⌜sf.readReg64 .x0 = 1#64⌝ ∗
          (⌜sf.readReg64 .x1 ≠ 0#64⌝ ∗
            (⌜sf.trace = s0.trace⌝ ∗ (y.bufRef ↦₆₄ y.slot) ∗
              (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv y.bs evs⌝ ∗
                A.pool lim (M.stepEvents evs st) sf) ∗
              stackAt s0.sp (0x40 + errStack) ∗
              decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
              memRegion y.slot 16 ∗ (y.ptr ↦ₛ y.bs) ∗ R)) := by
        rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
        exact ⟨hx0, hx1, hmem3⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem4
  · dsimp only [withLsCodeLoaded, decodeVarintSlowBudgetSpecWithStack] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [withLsCodeLoaded, decodeVarintSlowBudgetSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [withLsCodeLoaded, decodeVarintSlowBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decode_varint_slow_placed_ok_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (herr_stk : 0x40 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim errStack)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecGen A lim errStack)) :=
  decodeVarintSlowGen_lscl_ok_of_session2
    (decode_varint_slow_placed_ok_with_stack_of_contract herr_stk hFrom)

theorem decode_varint_slow_placed_ok_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A lim)) :=
  decode_varint_slow_placed_ok_gen (errStack := decodeErrorHookStack) (by decide)
    (decodeErrorFromWithStack_of_decodeErrorFrom hFrom)

theorem decode_varint_slow_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A lim)) :=
  decode_varint_slow_placed_ok_of_contract (decode_error_from_placed_ok hshim halloc)

theorem decode_varint_slow_placed_ok_of_contract_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)) :=
  decode_varint_slow_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide) hFrom

theorem decode_varint_slow_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)) :=
  decode_varint_slow_placed_ok_of_contract_x (decode_error_from_placed_ok_x hshim halloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
