/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmas
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `prost::encoding::skip_field::<&mut &[u8]> [local#5]` (Cases 1–6)

Total-correctness (`RustCliAllocBudget M`) verification of the six non-group dispatch branches of
`prost::encoding::skip_field::<&mut &[u8]> [local#5]` under `[LibsignalPlacement]`, threading
`A.pool lim st s` and exact `SkipFieldEnv` allocation envelopes.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafAPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalProtoCodec (
  WireType decodeVarint decodeVarint_length skipBytes skipField
)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  SepWPp.of_sepWP_lscl SkipFieldGhost bv_len_sub_skip bv_ptr_add_skip bv_ptr_add_skip_top
  cbz_depth_succ cbz_depth_zero decodeErrorHookStackX memRegion_48_split
  pointsTo64_pair_entails_memRegion16 skipField_depth_zero skipField_succ_endGroup
  skipField_succ_lengthDelimited skipField_succ_sixtyFourBit skipField_succ_thirtyTwoBit
  skipField_succ_varint sliceCursorAfter sliceCursorAt ule_len_of_ge ule_len_of_lt w0_and_255_eq
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.CliHandshake.Placed (blkPl_507 lsProg_507)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  skipBelow3_err skipBelow3_err_entails skipBelow3_leaf skipBelow3_leaf_entails stackAt_skipField3
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (SkipFieldEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux (
  call_frame_budget_lscl fitsEnv_decodeErrorFrom_of_skipField_none
  fitsEnv_varintSlice_of_skipField skipFieldEnv_nil_of_some skipFieldEnv_of_decodeErrorFrom
  skipFieldEnv_of_varintSlice_none varintSliceEnv_some_eq_nil
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget (
  skipField3SpecAt
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp, local arm64_norm]
private theorem bv64_sub_zero_pl (x : BitVec 64) : x - 0#64 = x := BitVec.sub_zero x

@[local simp, local arm64_norm]
private theorem bv64_add_zero_pl (x : BitVec 64) : x + 0#64 = x := BitVec.add_zero x

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

private theorem lscl_of_cl {α : Type} {P : Program} {pl : Obj.MultiPlacement}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl pl spec)) :
    subroutine_ok P entry (withLsCodeLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

/-- Case-restricted relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::skip_field::<&mut &[u8]> [local#5]` (Block `510`, `lsmpl.base 510`) at recursion
budget `depth` under predicate `P`. -/
def SkipField6AtPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) (depth : Nat) (P : SkipFieldGhost → Prop) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 510)
    (withLsCl lsmpl (skipField3SpecAt A lim depth P))

/-! ## Case 1: `depth = 0` (`RecursionLimitReached`) -/

set_option maxHeartbeats 800000 in
theorem skipField6_depth_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX))) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim 0 (fun _ => True))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ 0 (by decide),
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hdepth_eq : depth = 0 := by assumption
  subst hdepth_eq
  have hd_zero : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = 0#32 := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨wt, tag, 0, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_zero hd_zero
  have hnone := skipField_depth_zero (2 * bs.length + 2) tag wt bs
  have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none
    (x := ⟨wt, tag, 0, bufRef, slot, ptr, bs⟩) hnone hfits
  rw [hnone]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp 0 (by decide)]
  wp_reach
  intro hcl1
  refine call_frame_budget_lscl
    (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
    (x := (s0.sp - 96#64, 0x8000000000000002#64, st))
    (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000002#64 ∧
      FitsEnv M lim st DecodeErrorFromEnv)
    (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
    ⟨rfl, by decide, hfits_de⟩
    (by sep_focus)
    ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply SepWP.exists_elim; intro evs
  wp_pull_pures
  have hevs_de : DecodeErrorFromEnv evs := by assumption
  have hevs_sf := skipFieldEnv_of_decodeErrorFrom
    (x := ⟨wt, tag, 0, bufRef, slot, ptr, bs⟩) hnone hevs_de
  apply SepWP.fold (skipBelow3_err_entails s0.sp 0 (by decide)) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

/-! ## Case 2: `depth = d + 1`, `wt = .endGroup` (`UnexpectedEndGroupTag`) -/

set_option maxHeartbeats 800000 in
theorem skipField6_endGroup_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .endGroup))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hwt_eq : wt = .endGroup := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.endGroup.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.endGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  have hnone := skipField_succ_endGroup (2 * bs.length + 1) d tag bs
  have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none
    (x := ⟨.endGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hfits
  rw [hnone]
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
  conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v_err0
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
  conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
  wp_reach
  intro hcl1
  refine call_frame_budget_lscl
    (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
    (x := (s0.sp - 96#64, 0x8000000000000009#64, st))
    (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000009#64 ∧
      FitsEnv M lim st DecodeErrorFromEnv)
    (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
    ⟨rfl, by decide, hfits_de⟩
    (by sep_focus)
    ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved, arm64_norm] at hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  apply SepWP.exists_elim; intro evs
  wp_pull_pures
  have hevs_de : DecodeErrorFromEnv evs := by assumption
  have hevs_sf := skipFieldEnv_of_decodeErrorFrom
    (x := ⟨.endGroup, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hevs_de
  apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  wp_done

/-! ## Case 3: `depth = d + 1`, `wt = .sixtyFourBit` (`skipBytes 8`) -/

set_option maxHeartbeats 800000 in
theorem skipField6_sixtyFourBit_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .sixtyFourBit))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .sixtyFourBit := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.sixtyFourBit.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.sixtyFourBit, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  by_cases hlt : bs.length < 8
  · have hule := ule_len_of_lt (n := 8#64) hlt hlen_lt
    have hnone : skipField (2 * bs.length + 2) (d + 1) tag .sixtyFourBit bs = none := by
      rw [skipField_succ_sixtyFourBit]; simp [skipBytes, hlt]
    have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none
      (x := ⟨.sixtyFourBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hfits
    rw [hnone]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl
      (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
      (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
      (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
      ⟨rfl, by decide, hfits_de⟩
      (by sep_focus)
      ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_sf := skipFieldEnv_of_decodeErrorFrom
      (x := ⟨.sixtyFourBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hevs_de
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  · have hule := ule_len_of_ge (n := 8#64) hlt hlen_lt
    have hsub := bv_len_sub_skip (n := 8#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 8#64) hlt
    have hsome : skipField (2 * bs.length + 2) (d + 1) tag .sixtyFourBit bs = some (bs.drop 8) := by
      rw [skipField_succ_sixtyFourBit]; simp [skipBytes, hlt]
    have hevs_sf := skipFieldEnv_nil_of_some
      (x := ⟨.sixtyFourBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hsome
    rw [hsome]
    simp only [sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    conv => arg 4; rw [hpool_nil]
    wp_done

/-! ## Case 4: `depth = d + 1`, `wt = .thirtyTwoBit` (`skipBytes 4`) -/

set_option maxHeartbeats 800000 in
theorem skipField6_thirtyTwoBit_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .thirtyTwoBit))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .thirtyTwoBit := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.thirtyTwoBit.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.thirtyTwoBit, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  by_cases hlt : bs.length < 4
  · have hule := ule_len_of_lt (n := 4#64) hlt hlen_lt
    have hnone : skipField (2 * bs.length + 2) (d + 1) tag .thirtyTwoBit bs = none := by
      rw [skipField_succ_thirtyTwoBit]; simp [skipBytes, hlt]
    have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none
      (x := ⟨.thirtyTwoBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hfits
    rw [hnone]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro v_err0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl
      (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
      (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
      (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
      ⟨rfl, by decide, hfits_de⟩
      (by sep_focus)
      ?_
    intro sm hpcm hrunm hspm hcsm _hcl2
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    apply SepWPp.of_sepWP_ret
    simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_sf := skipFieldEnv_of_decodeErrorFrom
      (x := ⟨.thirtyTwoBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hevs_de
    apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  · have hule := ule_len_of_ge (n := 4#64) hlt hlen_lt
    have hsub := bv_len_sub_skip (n := 4#64) hlt
    have hadd := bv_ptr_add_skip_top (ptr := ptr) (n := 4#64) hlt
    have hsome : skipField (2 * bs.length + 2) (d + 1) tag .thirtyTwoBit bs = some (bs.drop 4) := by
      rw [skipField_succ_thirtyTwoBit]; simp [skipBytes, hlt]
    have hevs_sf := skipFieldEnv_nil_of_some
      (x := ⟨.thirtyTwoBit, tag, d + 1, bufRef, slot, ptr, bs⟩) hsome
    rw [hsome]
    simp only [sliceCursorAfter]
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    conv => arg 4; rw [hpool_nil]
    wp_done

/-! ## Case 5: `depth = d + 1`, `wt = .varint` -/

set_option maxHeartbeats 800000 in
theorem skipField6_varint_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .varint))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .varint := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.varint.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  have himp_none : decodeVarint bs = none →
      skipField (2 * bs.length + 2) (d + 1) tag .varint bs = none := by
    intro hd; rw [skipField_succ_varint, hd]; rfl
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env bs) :=
    fitsEnv_varintSlice_of_skipField
      (x := ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩) himp_none hfits
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl0
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps_sync_pool (lsmpl.base 515)
  simp only [State.setMem_setMem]
  wp_reach
  intro hcl1
  refine call_frame_budget_lscl (spec := decodeVarint2SpecX A lim)
    (x := (⟨bufRef, slot, ptr, bs⟩, st))
    (φ := bufRef = bufRef ∧ bs.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env bs))
    (ret_pc := (blkPl_507).base + 112#64) (lscl_of_cl hVarintCall) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeVarint2SpecX, arm64_norm]; rfl)
    ⟨rfl, hlen_lt, hfits_dv⟩
    (by simp only [sliceCursorAt]; sep_focus)
    ?_
  intro sm hpcm hrunm hspm hcsm _hcl2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  cases hd : decodeVarint bs with
  | none =>
    have hnone := himp_none hd
    rw [hnone]
    simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_dv : DecodeVarint2Env bs evs := by assumption
    have hevs_sf := skipFieldEnv_of_varintSlice_none
      (x := ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩) hd hnone hevs_dv
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  | some p =>
    rcases p with ⟨v, rest⟩
    have hsome : skipField (2 * bs.length + 2) (d + 1) tag .varint bs = some rest := by
      rw [skipField_succ_varint, hd]; rfl
    rw [hsome]
    simp only [decodeVarint2SpecX, hd, sliceCursorAfter,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_dv : DecodeVarint2Env bs evs := by assumption
    have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
    subst hevs0
    have hevs_sf := skipFieldEnv_nil_of_some
      (x := ⟨.varint, tag, d + 1, bufRef, slot, ptr, bs⟩) hsome
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done

/-! ## Case 6: `depth = d + 1`, `wt = .lengthDelimited` -/

set_option maxHeartbeats 1200000 in
theorem skipField6_lengthDelimited_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_507 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hVarintCall : subroutine_ok (lsProg_507 H) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)))
    (d : Nat) (hdepth : d + 1 < 2 ^ 32) :
    subroutine_ok (lsProg_507 H) (blkPl_507).base
      (withLsCodeLoaded lsmpl (skipField3SpecAt A lim (d + 1) (fun x => x.wt = .lengthDelimited))) := by
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold skipField3SpecAt
    simp only [sliceCursorAt, stackAt_skipField3 _ (d + 1) hdepth,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, tag, depth, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hwt_eq : wt = .lengthDelimited := by assumption
  subst hwt_eq
  have hdepth_eq : depth = d + 1 := by assumption
  subst hdepth_eq
  have hx0_wt : BitVec.setWidth 8 (s0.readReg64 (Reg.gpr 0#5)) = BitVec.ofNat 8 WireType.lengthDelimited.toNat := by assumption
  have hx3_d : BitVec.setWidth 32 (s0.readReg64 (Reg.gpr 3#5)) = BitVec.ofNat 32 (d + 1) := by assumption
  have hfits : FitsEnv M lim st (SkipFieldEnv ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) := by assumption
  have hcbz := cbz_depth_succ hx3_d hdepth
  have hw0 := w0_and_255_eq hx0_wt
  dsimp [WireType.toNat] at hw0
  have himp_none : decodeVarint bs = none →
      skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs = none := by
    intro hd; rw [skipField_succ_lengthDelimited, hd]
  have hfits_dv : FitsEnv M lim st (DecodeVarint2Env bs) :=
    fitsEnv_varintSlice_of_skipField
      (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) himp_none hfits
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 515) hcl0
  conv => arg 4; rw [skipBelow3_leaf s0.sp (d + 1) hdepth]
  wp_steps_sync_pool (lsmpl.base 515)
  simp only [State.setMem_setMem]
  wp_reach
  intro hcl1
  refine call_frame_budget_lscl (spec := decodeVarint2SpecX A lim)
    (x := (⟨bufRef, slot, ptr, bs⟩, st))
    (φ := bufRef = bufRef ∧ bs.length < 2 ^ 63 ∧ FitsEnv M lim st (DecodeVarint2Env bs))
    (ret_pc := (blkPl_507).base + 160#64) (lscl_of_cl hVarintCall) hcl1
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [decodeVarint2SpecX, arm64_norm]; rfl)
    ⟨rfl, hlen_lt, hfits_dv⟩
    (by simp only [sliceCursorAt]; sep_focus)
    ?_
  intro sm hpcm hrunm hspm hcsm hcl2
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm]
    at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  cases hd : decodeVarint bs with
  | none =>
    have hnone := himp_none hd
    rw [hnone]
    apply SepWPp.of_sepWP_ret
    simp only [decodeVarint2SpecX, hd, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_dv : DecodeVarint2Env bs evs := by assumption
    have hevs_sf := skipFieldEnv_of_varintSlice_none
      (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hd hnone hevs_dv
    apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  | some p =>
    rcases p with ⟨len, rest⟩
    have hrest_le : rest.length ≤ bs.length := Nat.le_of_lt (decodeVarint_length hd)
    have hrest_lt : rest.length < 2 ^ 63 := by omega
    by_cases hlt : rest.length < len.toNat
    · have hule := ule_len_of_lt hlt hrest_lt
      have hnone : skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs = none := by
        rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
      have hfits_de := fitsEnv_decodeErrorFrom_of_skipField_none
        (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hfits
      rw [hnone]
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl2
      simp only [decodeVarint2SpecX, hd, sliceCursorAfter,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
      have hsm1 : sm.readReg64 (Reg.gpr 1#5) = len := by assumption
      have htrm : sm.trace = s0.trace := by assumption
      have hevs_dv : DecodeVarint2Env bs evs := by assumption
      have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
      subst hevs0
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      conv => arg 4; rw [memRegion_48_split (s0.sp - 96#64), bv_sub_add_lit s0.sp 96 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps_sync_pool (lsmpl.base 261)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot
        (ptr + BitVec.ofNat 64 (bs.length - rest.length)) (BitVec.ofNat 64 rest.length)) (by sep_focus)
      conv => arg 4; rw [skipBelow3_err s0.sp (d + 1) hdepth, ← hspm]
      wp_reach
      intro hcl3
      refine call_frame_budget_lscl
        (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
        (x := (s0.sp - 96#64, 0x8000000000000007#64, st))
        (φ := s0.sp - 96#64 = s0.sp - 96#64 ∧ KindNoHeap 0x8000000000000007#64 ∧
          FitsEnv M lim st DecodeErrorFromEnv)
        (ret_pc := (blkPl_507).base + 204#64) (lscl_of_cl hFromCall) hcl3
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrunm])
        (by simp only [State.spAligned, hspm, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
        ⟨rfl, by decide, hfits_de⟩
        (by sep_focus)
        ?_
      intro sm2 hpcm2 hrunm2 hspm2 hcsm2 _hcl4
      simp only [CalleeSavedPreserved] at hcsm2
      obtain ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩ := hcsm2
      simp (config := { decide := true }) only [arm64_norm, hspm,
        hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs]
        at hpcm2 hspm2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply SepWPp.of_sepWP_ret
      simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
        arm64_norm, htrm, hspm]
      apply SepWP.exists_elim; intro evs2
      wp_pull_pures
      have hevs_de : DecodeErrorFromEnv evs2 := by assumption
      have hevs_sf := skipFieldEnv_of_decodeErrorFrom
        (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hnone hevs_de
      apply SepWP.fold (skipBelow3_err_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done
    · have hule := ule_len_of_ge hlt hrest_lt
      have hsub := bv_len_sub_skip hlt
      have hadd := bv_ptr_add_skip (ptr := ptr) hrest_le hlt
      have hsome : skipField (2 * bs.length + 2) (d + 1) tag .lengthDelimited bs =
          some (rest.drop len.toNat) := by
        rw [skipField_succ_lengthDelimited, hd]; simp [skipBytes, hlt]
      rw [hsome]
      apply SepWPp.of_sepWP_ret
      simp only [decodeVarint2SpecX, hd, sliceCursorAfter,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hsm0 : sm.readReg64 (Reg.gpr 0#5) = 0#64 := by assumption
      have hsm1 : sm.readReg64 (Reg.gpr 1#5) = len := by assumption
      have htrm : sm.trace = s0.trace := by assumption
      have hevs_dv : DecodeVarint2Env bs evs := by assumption
      have hevs0 := varintSliceEnv_some_eq_nil hd hevs_dv
      subst hevs0
      have hevs_sf := skipFieldEnv_nil_of_some
        (x := ⟨.lengthDelimited, tag, d + 1, bufRef, slot, ptr, bs⟩) hsome
      apply SepWP.fold (skipBelow3_leaf_entails s0.sp (d + 1) hdepth) (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafAPlacedBudget
