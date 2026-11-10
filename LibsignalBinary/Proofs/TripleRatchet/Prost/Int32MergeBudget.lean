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
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of `prost::encoding::int32::merge::<&mut &[u8]>`

Relocatable `RustCliAllocBudget`-threaded verification of `prost::encoding::int32::merge::<&mut &[u8]>`
(block 8) and re-exports for `decode_varint_slow::<&mut &[u8]>` (block 293).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustAllocEvents rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   blkPC_8 blkPl_8 blkPC_76 blkPl_76 blkPC_261 blkPl_261 blkPC_293 blkPl_293
   lsRustAllocSym lsRustNoAllocShimSym
   ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux mergeUint32)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack extHookStack varintSlow varintSlowAux)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
  (decodeVarintAux_suffix decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (DecodeVarintSlowGhost Int32MergeGhost SepWPp.call_frame_lscl SepWPp.of_sepWP_lscl VarintSlicePre
   bv_len_sub_consumed cbz_len_cons_false decodeErrorHookStackX
   getLsbD_7_of_gt getLsbD_7_of_le len_cons_sub_one len_ult_consumed_false
   memRegion_48_slice memRegion_48_split memRegion_48_wtErr
   mergeUint32_ne_varint mergeUint32_varint_1
   pointsTo64_pair_entails_memRegion16 pointsToBytes_split_last
   signExtend64_getLsbD_63_of_gt signExtend64_getLsbD_63_of_le
   sliceCursorAfter sliceCursorAt sliceErr_entails_memRegion48 sliceOk_entails_memRegion48
   stackAt_int32MergeGen stackAt_sliceGen_eq_errorHookGen stackAt_sliceGen_eq_slowGen
   ult_10_of_ge_11 ult_10_of_lt_11
   varintSliceResultAt wtErr_entails_memRegion40
   wt_beq_zero_of_ne_varint wt_beq_zero_of_varint)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (DecodeVarintSlowEnv decodeVarintSlowBudgetSpecWithStack decodeVarintSlowEvents
   sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (decodeErrorFromWithStack_of_decodeErrorFrom decodeVarintSlowSpecWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv Int32MergeEnv Int32MergePlacedOk Int32MergePlacedOkX
   decodeVarintSliceEvents decodeVarintSliceSpec decodeVarintSliceSpecGen decodeVarintSliceSpecX
   int32MergeEvents int32MergeSpec int32MergeSpecGen int32MergeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok decode_error_from_placed_ok_x
   decode_varint_slice_placed_ok decode_varint_slice_placed_ok_x)

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

local macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *]))

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

/-! ## `decodeVarintSlowSpecGen` re-exports and envelope bridge lemmas -/

export LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
  (decodeVarintSlowSpecGen decodeVarintSlowSpec decodeVarintSlowSpecX
   decode_varint_slow_placed_ok_with_stack
   decode_varint_slow_placed_ok_with_stack_of_contract
   decode_varint_slow_placed_ok_with_stack_of_hooks
   decode_varint_slow_placed_ok_with_stack_x
   decodeVarintSlowGen_lscl_ok_of_session2
   decode_varint_slow_placed_ok_gen
   decode_varint_slow_placed_ok_of_contract
   decode_varint_slow_placed_ok
   decode_varint_slow_placed_ok_of_contract_x
   decode_varint_slow_placed_ok_x)

private theorem int32MergeEvents_varint_eq_slice (bs : List (BitVec 8)) :
    int32MergeEvents .varint bs = decodeVarintSliceEvents bs := by
  simp only [int32MergeEvents, decodeVarintSliceEvents, mergeUint32, ne_eq, not_true_eq_false, ite_false]
  cases decodeVarint bs <;> rfl

private theorem decodeVarintSlowEvents_eq_slice (bs : List (BitVec 8)) :
    decodeVarintSlowEvents bs = decodeVarintSliceEvents bs := by
  simp only [decodeVarintSlowEvents, decodeVarintSliceEvents, decodeVarint_eq_varintSlow bs]
  cases decodeVarint bs <;> rfl

private theorem int32MergeEvents_varint_eq_slow (bs : List (BitVec 8)) :
    int32MergeEvents .varint bs = decodeVarintSlowEvents bs :=
  (int32MergeEvents_varint_eq_slice bs).trans (decodeVarintSlowEvents_eq_slice bs).symm

/-! ## Relocatable `prost::encoding::int32::merge::<&mut &[u8]>` (block 8) -/

set_option maxHeartbeats 1600000 in
theorem int32_merge_placed_ok_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (herr : 0x50 + (0x50 + errStack) ≤ 2 ^ 64)
    (hFromCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim errStack)))
    (hSlowCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecGen A lim errStack)))
    (hSliceCall : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (lsmpl.base 76)
      (withLsCl lsmpl (decodeVarintSliceSpecGen A lim errStack))) :
    subroutine_ok ((blkPC_8).rebase (blkPl_8).base H)
      (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpecGen A lim errStack)) := by
  have herrSlice : 0x50 + errStack ≤ 2 ^ 64 := by omega
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold int32MergeSpecGen
    simp only [sliceCursorAt, stackAt_int32MergeGen herr, sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨wt, valPtr, bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have h_1 : (s0.readReg64 (Reg.gpr 0#5)).setWidth 8 = BitVec.ofNat 8 wt.toNat := by assumption
  have h : bs.length < 2 ^ 63 := by assumption
  have hfits : FitsEnv M lim st (Int32MergeEnv ⟨wt, valPtr, bufRef, slot, ptr, bs⟩) := by assumption
  by_cases hwt : wt = .varint
  · subst hwt
    have hwt_br := wt_beq_zero_of_varint h_1
    cases bs with
    | nil =>
      have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
        refine hfits.mono fun evs he => ?_
        simpa only [Int32MergeEnv, int32MergeEvents, mergeUint32, decodeVarint, decodeVarintAux,
          ne_eq, not_true_eq_false, ite_false, DecodeErrorFromEnv] using he
      simp only [mergeUint32, decodeVarint, decodeVarintAux, ne_eq, not_true_eq_false, ite_false]
      apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
      conv => arg 4; rw [memRegion_48_split (s0.sp - 80#64), bv_sub_add_lit s0.sp 80 8]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v_err0
      wp_steps_sync_pool (lsmpl.base 261)
      simp only [State.setMem_setMem]
      apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr 0#64) (by sep_focus)
      conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
      wp_reach
      intro hcl1
      refine SepWPp.call_frame_lscl (pl := lsmpl)
        (spec := decodeErrorFromBudgetSpecWithStack M A lim errStack)
        (x := (s0.sp - 80#64, 0x8000000000000001#64, st))
        (φ := s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000001#64 ∧
          FitsEnv M lim st DecodeErrorFromEnv)
        (ret_pc := (blkPl_8).base + bv% (52)) hFromCall hcl1
        (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
        (by simp only [arm64_norm])
        (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
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
      simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
        arm64_norm]
      apply SepWP.exists_elim; intro evs
      wp_pull_pures
      have hevs_de : DecodeErrorFromEnv evs := by assumption
      have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, []⟩ evs := by
        simpa only [Int32MergeEnv, int32MergeEvents, mergeUint32, decodeVarint, decodeVarintAux,
          ne_eq, not_true_eq_false, ite_false, DecodeErrorFromEnv] using hevs_de
      apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm)
        (by sep_focus)
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      wp_done
    | cons b0 bs1 =>
      have hcbz := cbz_len_cons_false h
      by_cases hb0 : b0 ≤ 0x7f#8
      · have hbit0 := signExtend64_getLsbD_63_of_le hb0
        have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ [] := by
          simp only [Int32MergeEnv, int32MergeEvents, mergeUint32_varint_1 bs1 hb0]
        rw [mergeUint32_varint_1 bs1 hb0]
        apply SepWPp.of_sepWP_ret
        conv => arg 4; rw [pointsToBytes_cons, memRegion_four valPtr]
        simp only [sepExists_sepConj_left]
        apply SepWP.exists_elim; intro v_val
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq (congrArg ((slot + 8#64) ↦₆₄ ·) (len_cons_sub_one b0 bs1)))
          (by sep_focus)
        have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
        conv => arg 4; rw [hpool_nil]
        conv => arg 5; simp only [sliceCursorAfter, List.length_cons, Nat.add_sub_cancel_left, arm64_norm]
        wp_done
      · have hbit0 := signExtend64_getLsbD_63_of_gt hb0
        have hlen_toNat : (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hfits_slice : FitsEnv M lim st (DecodeVarintSliceEnv (b0 :: bs1)) := by
          refine hfits.mono fun evs he => ?_
          simpa only [Int32MergeEnv, DecodeVarintSliceEnv,
            int32MergeEvents_varint_eq_slice (b0 :: bs1)] using he
        have hfits_slow : FitsEnv M lim st (DecodeVarintSlowEnv (b0 :: bs1)) := by
          refine hfits.mono fun evs he => ?_
          simpa only [Int32MergeEnv, DecodeVarintSlowEnv,
            int32MergeEvents_varint_eq_slow (b0 :: bs1)] using he
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_8).base + bv% (144)) hcl0
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps_sync_pool ((blkPl_8).base + bv% (144))
        simp only [State.setMem_setMem]
        wp_reach
        intro hcl1
        by_cases h11 : 11 ≤ (b0 :: bs1).length
        · have hhi := ult_10_of_ge_11 h11 h
          have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inl h11
          apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl1
          conv => arg 4; rw [memRegion_48_slice s0.sp]
          wp_steps_sync_pool (lsmpl.base 76)
          simp only [State.setMem_setMem]
          wp_reach
          intro hcl2
          refine SepWPp.call_frame_lscl (pl := lsmpl)
            (spec := decodeVarintSliceSpecGen A lim errStack)
            (x := (⟨s0.sp - 80#64, ptr, b0 :: bs1⟩, st))
            (φ := s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
              (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
              (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1) ∧
              FitsEnv M lim st (DecodeVarintSliceEnv (b0 :: bs1)))
            (ret_pc := (blkPl_8).base + bv% (176)) hSliceCall hcl2
            (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
            (by simp only [arm64_norm])
            (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
            ⟨rfl, rfl, hlen_toNat, h, hpre_slice, hfits_slice⟩
            (by sep_focus)
            (fun _ _ _ _ hex => by
              simp only [decodeVarintSliceSpecGen] at hex
              exact not_satisfies_false_sepConj hex)
            (fun _ _ hpan => by
              simp only [decodeVarintSliceSpecGen, sepConj_assoc] at hpan
              exact False.elim (not_satisfies_false_sepConj hpan))
            ?_
          intro sm hpcm hrunm hspm hcsm _
          simp only [CalleeSavedPreserved] at hcsm
          obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
          simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
          apply SepWPp.of_sepWP_ret
          cases hd : decodeVarint (b0 :: bs1) with
          | none =>
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
              varintSliceResultAt, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
            apply SepWP.exists_elim; intro evs
            apply SepWP.exists_elim; intro e_err
            wp_pull_pures
            have hevs_vs : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
            have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
              simpa only [Int32MergeEnv, DecodeVarintSliceEnv,
                int32MergeEvents_varint_eq_slice (b0 :: bs1)] using hevs_vs
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length))
              (by sep_focus)
            apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
            wp_done
          | some p =>
            rcases p with ⟨v, rest⟩
            have hcc := len_ult_consumed_false (rest := rest) h
            have hsub_len := bv_len_sub_consumed hd
            simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
              varintSliceResultAt, sliceCursorAfter, sepExists_sepConj_left, sepExists_sepConj_right,
              arm64_norm]
            apply SepWP.exists_elim; intro evs
            wp_pull_pures
            have hevs_vs : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
            have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
              simpa only [Int32MergeEnv, DecodeVarintSliceEnv,
                int32MergeEvents_varint_eq_slice (b0 :: bs1)] using hevs_vs
            conv => arg 4; rw [memRegion_four valPtr]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            apply SepWP.exists_elim; intro v_val
            wp_steps_sync_pool (s0.readReg64 Reg.lr)
            simp only [State.setMem_setMem]
            apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)))
              (by sep_focus)
            wp_done
        · have hhi := ult_10_of_lt_11 h11 h
          have hne_cons : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_8).base + bv% (156)) hcl1
          apply SepWP.fold (Entails.of_eq (pointsToBytes_cons ptr b0 bs1).symm) (by sep_focus)
          conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h]
          wp_steps_sync_pool ((blkPl_8).base + bv% (156))
          simp only [State.setMem_setMem]
          apply SepWP.fold (Entails.of_eq (pointsToBytes_split_last ptr (b0 :: bs1) hne_cons h).symm) (by sep_focus)
          wp_reach
          intro hcl2
          by_cases hlast : ((b0 :: bs1).getLast hne_cons).toNat ≤ 0x7F
          · have hbit_last := getLsbD_7_of_le hlast
            have hpre_slice : VarintSlicePre (b0 :: bs1) := Or.inr ⟨hne_cons, hlast⟩
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 76) hcl2
            conv => arg 4; rw [pointsToBytes_cons, memRegion_48_slice s0.sp]
            wp_steps_sync_pool (lsmpl.base 76)
            simp only [State.setMem_setMem]
            wp_reach
            intro hcl3
            refine SepWPp.call_frame_lscl (pl := lsmpl)
              (spec := decodeVarintSliceSpecGen A lim errStack)
              (x := (⟨s0.sp - 80#64, ptr, b0 :: bs1⟩, st))
              (φ := s0.sp - 80#64 = s0.sp - 80#64 ∧ ptr = ptr ∧
                (BitVec.ofNat 64 (b0 :: bs1).length).toNat = (b0 :: bs1).length ∧
                (b0 :: bs1).length < 2 ^ 63 ∧ VarintSlicePre (b0 :: bs1) ∧
                FitsEnv M lim st (DecodeVarintSliceEnv (b0 :: bs1)))
              (ret_pc := (blkPl_8).base + bv% (176)) hSliceCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSliceSpecGen, arm64_norm]; rfl)
              ⟨rfl, rfl, hlen_toNat, h, hpre_slice, hfits_slice⟩
              (by sep_focus)
              (fun _ _ _ _ hex => by
                simp only [decodeVarintSliceSpecGen] at hex
                exact not_satisfies_false_sepConj hex)
              (fun _ _ hpan => by
                simp only [decodeVarintSliceSpecGen, sepConj_assoc] at hpan
                exact False.elim (not_satisfies_false_sepConj hpan))
              ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                varintSliceResultAt, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
              apply SepWP.exists_elim; intro evs
              apply SepWP.exists_elim; intro e_err
              wp_pull_pures
              have hevs_vs : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
                simpa only [Int32MergeEnv, DecodeVarintSliceEnv,
                  int32MergeEvents_varint_eq_slice (b0 :: bs1)] using hevs_vs
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 (b0 :: bs1).length))
                (by sep_focus)
              apply SepWP.fold (sliceErr_entails_memRegion48 s0.sp 1#64 e_err) (by sep_focus)
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              have hcc := len_ult_consumed_false (rest := rest) h
              have hsub_len := bv_len_sub_consumed hd
              simp only [decodeVarintSliceSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                varintSliceResultAt, sliceCursorAfter, sepExists_sepConj_left, sepExists_sepConj_right,
                arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hevs_vs : DecodeVarintSliceEnv (b0 :: bs1) evs := by assumption
              have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
                simpa only [Int32MergeEnv, DecodeVarintSliceEnv,
                  int32MergeEvents_varint_eq_slice (b0 :: bs1)] using hevs_vs
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              apply SepWP.fold (sliceOk_entails_memRegion48 s0.sp 0#64 v (BitVec.ofNat 64 ((b0 :: bs1).length - rest.length)))
                (by sep_focus)
              wp_done
          · have hbit_last := getLsbD_7_of_gt hlast
            apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl2
            wp_steps_sync_pool (lsmpl.base 293)
            simp only [State.setMem_setMem]
            conv => arg 4; rw [stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)]
            wp_reach
            intro hcl3
            refine SepWPp.call_frame_lscl (pl := lsmpl)
              (spec := decodeVarintSlowSpecGen A lim errStack)
              (x := (⟨bufRef, slot, ptr, b0 :: bs1⟩, st))
              (φ := bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63 ∧
                FitsEnv M lim st (DecodeVarintSlowEnv (b0 :: bs1)))
              (ret_pc := (blkPl_8).base + bv% (268)) hSlowCall hcl3
              (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
              (by simp only [arm64_norm])
              (by simp only [decodeVarintSlowSpecGen, arm64_norm]; rfl)
              ⟨rfl, h, hfits_slow⟩
              (by simp only [sliceCursorAt]; sep_focus)
              (fun _ _ _ _ hex => by
                simp only [decodeVarintSlowSpecGen] at hex
                exact not_satisfies_false_sepConj hex)
              (fun _ _ hpan => by
                simp only [decodeVarintSlowSpecGen, sepConj_assoc] at hpan
                exact False.elim (not_satisfies_false_sepConj hpan))
              ?_
            intro sm hpcm hrunm hspm hcsm _
            simp only [CalleeSavedPreserved] at hcsm
            obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
            simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
            apply SepWPp.of_sepWP_ret
            cases hd : decodeVarint (b0 :: bs1) with
            | none =>
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hevs_sl : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
              have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
                simpa only [Int32MergeEnv, DecodeVarintSlowEnv,
                  int32MergeEvents_varint_eq_slow (b0 :: bs1)] using hevs_sl
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm)
                (by sep_focus)
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done
            | some p =>
              rcases p with ⟨v, rest⟩
              simp only [decodeVarintSlowSpecGen, mergeUint32, hd, ne_eq, not_true_eq_false, ite_false,
                sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
              apply SepWP.exists_elim; intro evs
              wp_pull_pures
              have hevs_sl : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
              have hevs_im : Int32MergeEnv ⟨.varint, valPtr, bufRef, slot, ptr, b0 :: bs1⟩ evs := by
                simpa only [Int32MergeEnv, DecodeVarintSlowEnv,
                  int32MergeEvents_varint_eq_slow (b0 :: bs1)] using hevs_sl
              apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_slowGen herrSlice (s0.sp - 80#64)).symm)
                (by sep_focus)
              conv => arg 4; rw [memRegion_four valPtr]
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              apply SepWP.exists_elim; intro v_val
              wp_steps_sync_pool (s0.readReg64 Reg.lr)
              simp only [State.setMem_setMem]
              wp_done
  · have hwt_br := wt_beq_zero_of_ne_varint h_1 hwt
    have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
      refine hfits.mono fun evs he => ?_
      simpa only [Int32MergeEnv, int32MergeEvents, mergeUint32_ne_varint bs hwt,
        DecodeErrorFromEnv] using he
    rw [mergeUint32_ne_varint bs hwt]
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    conv => arg 4; rw [memRegion_48_wtErr s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro b_err1
    apply SepWP.exists_elim; intro b_err0
    apply SepWP.exists_elim; intro v_err0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (wtErr_entails_memRegion40 s0.sp _ _) (by sep_focus)
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 bs.length)) (by sep_focus)
    conv => arg 4; rw [stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)]
    wp_reach
    intro hcl1
    refine SepWPp.call_frame_lscl (pl := lsmpl)
      (spec := decodeErrorFromBudgetSpecWithStack M A lim errStack)
      (x := (s0.sp - 80#64, 0x8000000000000006#64, st))
      (φ := s0.sp - 80#64 = s0.sp - 80#64 ∧ KindNoHeap 0x8000000000000006#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_8).base + bv% (52)) hFromCall hcl1
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm]; rfl)
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
    simp only [decodeErrorFromBudgetSpecWithStack, sepExists_sepConj_left, sepExists_sepConj_right,
      arm64_norm]
    apply SepWP.exists_elim; intro evs
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_im : Int32MergeEnv ⟨wt, valPtr, bufRef, slot, ptr, bs⟩ evs := by
      simpa only [Int32MergeEnv, int32MergeEvents, mergeUint32_ne_varint bs hwt,
        DecodeErrorFromEnv] using hevs_de
    apply SepWP.fold (Entails.of_eq (stackAt_sliceGen_eq_errorHookGen herrSlice (s0.sp - 80#64)).symm)
      (by sep_focus)
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done

theorem int32_merge_placed_ok_of_contracts [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpec M A lim))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpec A lim)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpec A lim))) :
    Int32MergePlacedOk A lim H :=
  int32_merge_placed_ok_gen (errStack := decodeErrorHookStack) (by decide)
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_8).rebase (blkPl_8).base H)
      (decodeErrorFromWithStack_of_decodeErrorFrom hFrom))
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlow)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

theorem int32_merge_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    Int32MergePlacedOk A lim H :=
  int32_merge_placed_ok_of_contracts
    (decode_error_from_placed_ok hshim halloc)
    (decode_varint_slow_placed_ok hshim halloc)
    (decode_varint_slice_placed_ok hshim halloc)

theorem int32_merge_placed_ok_of_contracts_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim))) :
    Int32MergePlacedOkX A lim H :=
  int32_merge_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide)
    (ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_8).rebase (blkPl_8).base H) hFrom)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlow)
    (ls_subroutine_ok_cl_of_block (callerProg := (blkPC_8).rebase (blkPl_8).base H) hSlice)

theorem int32_merge_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    Int32MergePlacedOkX A lim H :=
  int32_merge_placed_ok_of_contracts_x
    (decode_error_from_placed_ok_x hshim halloc)
    (decode_varint_slow_placed_ok_x hshim halloc)
    (decode_varint_slice_placed_ok_x hshim halloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
