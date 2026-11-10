/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux
public meta import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Handshake `decode_varint [local#4]`

Verifies `[LibsignalPlacement]` `prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]`
(Block `515`) against `decodeVarint2SpecX A lim` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under
`FitsEnv`) from `GrowOneXBudget.AllocContractsPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_261 blkPl_261 blkPC_293 blkPl_293
  ls_subroutine_ok_cl_of_block lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet (KindNoHeap decodeErrorAtStackLen)
open CryptoVerification.LibsignalTripleRatchet.VarintBridge (decodeVarint_eq_varintSlow)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost SepWPp.of_sepWP_lscl VarintSlicePre
  byte9_ule_of_ge byte9_ule_of_lt cbz_len_cons_false
  decodeErrorHookStackX decodeVarintSlowStackX decodeVarint_eq_none_of_pre
  exists_cons_of_all_gt memRegion_48_split
  ovf_byte2 ovf_byte3 ovf_byte6 ovf_byte7 ovf_byte10
  pointsTo64_pair_entails_memRegion16 pointsToBytes_split_last
  sliceCursorAfter sliceCursorAt toNat_le_0x7f_iff two_le_toNat_iff
  ult_10_of_ge_11 ult_10_of_lt_11
)
open CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits (
  getLsbD_7_beq_of_gt getLsbD_7_beq_of_le ovf_byte4_zext ovf_byte8_zext
  signExtend64_getLsbD_63_beq_of_gt signExtend64_getLsbD_63_beq_of_le
)
open CryptoVerification.LibsignalTripleRatchet.Prost.X (decodeErrorHookStackW)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.CliHandshake.Placed (blkPl_515 lsProg_515)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  byte9_ult1_of_ge byte9_ult1_of_lt
  decodeVarint_1 decodeVarint_2 decodeVarint_3 decodeVarint_4 decodeVarint_5
  decodeVarint_6 decodeVarint_7 decodeVarint_8 decodeVarint_9 decodeVarint_10
  getLsbD_31_signExtend signExtend32_and_127 signExtend32_and_255
  sliceCursorAfter_of_eq stackAt_decodeVarint2X
  stackAt_errorHookX_entails_slowX stackAt_slowX_eq_errorHookX
  zeroExtend64_zeroExtend32
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv decodeErrorFromBudgetSpecWithStack
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromXBudget (
  decodeErrorFrom_placed_okW
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  DecodeVarintSlowEnv decodeVarintSlowEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudgetAux (
  decodeVarintSlowGen_lscl_ok_of_session2 decodeVarintSlowSpecGen decodeVarintSlowSpecX
  decode_varint_slow_placed_ok_with_stack
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudgetAux (
  call_frame_budget_lscl
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm]
  signExtend32_and_255 zeroExtend64_zeroExtend32 signExtend32_and_127 getLsbD_31_signExtend
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_64_align_pl (sp : BitVec 64) :
    ((sp - 64#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

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

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::varint::decode_varint::<&mut &[u8]> [local#4]`
(Block `515`, `(blkPl_515).base = lsmpl.base 515`) on `lsProg_518 ext`. -/
def DecodeVarint5PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
    (withLsCl lsmpl (decodeVarint2SpecX A lim))

/-! ## Envelope Bridge Helpers -/

private theorem fitsEnv_decodeErrorFrom_of_dv2_none {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)} (hd : decodeVarint bs = none)
    (hfits : FitsEnv M lim st (DecodeVarint2Env bs)) :
    FitsEnv M lim st DecodeErrorFromEnv :=
  hfits.mono fun evs he => by
    simpa only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd,
      DecodeErrorFromEnv] using he

private theorem dv2Env_of_decodeErrorFrom {bs : List (BitVec 8)} {evs : List AllocEvent}
    (hd : decodeVarint bs = none) (he : DecodeErrorFromEnv evs) :
    DecodeVarint2Env bs evs := by
  simpa only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd,
    DecodeErrorFromEnv] using he

private theorem dv2Env_nil_of_some {bs : List (BitVec 8)} {v : BitVec 64}
    {rest : List (BitVec 8)} (hd : decodeVarint bs = some (v, rest)) :
    DecodeVarint2Env bs [] := by
  simp only [DecodeVarint2Env, DecodeVarintSliceEnv, decodeVarintSliceEvents, hd]

private theorem fitsEnv_varintSlow_of_dv2 {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {bs : List (BitVec 8)}
    (hfits : FitsEnv M lim st (DecodeVarint2Env bs)) :
    FitsEnv M lim st (DecodeVarintSlowEnv bs) :=
  hfits.mono fun evs he => by
    cases hd : decodeVarint bs <;>
      simpa only [DecodeVarintSlowEnv, decodeVarintSlowEvents, DecodeVarint2Env,
        DecodeVarintSliceEnv, decodeVarintSliceEvents, decodeVarint_eq_varintSlow bs,
        hd, Option.map] using he

private theorem dv2Env_of_varintSlow {bs : List (BitVec 8)} {evs : List AllocEvent}
    (he : DecodeVarintSlowEnv bs evs) :
    DecodeVarint2Env bs evs := by
  cases hd : decodeVarint bs <;>
    simpa only [DecodeVarintSlowEnv, decodeVarintSlowEvents, DecodeVarint2Env,
      DecodeVarintSliceEnv, decodeVarintSliceEvents, decodeVarint_eq_varintSlow bs,
      hd, Option.map] using he

/-! ## Split Join Helpers at `(blkPl_515).base + 88#64` -/

private structure Dv5JoinAt (s0 s : State) (slot ptr : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) (entry : BitVec 64) : Prop where
  pc_eq : s.pc = entry + 88#64
  run_eq : s.status = .Running
  sp_eq : s.sp = s0.sp - 64#64
  sp_align : s.spAligned = true
  tr_eq : s.trace = s0.trace
  x1_eq : s.readReg64 (Reg.gpr 1#5) = BitVec.signExtend 64 b0
  x8_eq : s.readReg64 (Reg.gpr 8#5) = slot
  x9_eq : s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 (b0 :: b1 :: bs2).length
  x10_eq : s.readReg64 (Reg.gpr 10#5) = ptr
  x11_eq : s.readReg64 (Reg.gpr 11#5) =
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.signExtend 64 b1))
  x29_eq : s.readReg64 (Reg.gpr 29#5) = s0.sp - 16#64
  cs_19 : s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5)
  cs_20 : s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5)
  cs_21 : s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5)
  cs_22 : s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5)
  cs_23 : s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5)
  cs_24 : s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5)
  cs_25 : s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5)
  cs_26 : s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5)
  cs_27 : s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5)
  cs_28 : s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5)
  vregs_eq : calleeSavedVRegs s = calleeSavedVRegs s0

private theorem pointsToBytes_cons_zero (ptr : BitVec 64) (b : BitVec 8)
    (bs : List (BitVec 8)) (Q : SepProp) :
    ptr ↦₈ b ∗ ((ptr + 1#64) ↦ₛ bs ∗ Q) = ptr ↦ₛ (b :: bs) ∗ Q := by
  rw [← sepConj_assoc, ← pointsToBytes_cons]

private theorem pointsToBytes_split_off (ptr : BitVec 64) (k : Nat) (_hk1 : k + 1 < 2 ^ 64)
    (b : BitVec 8) (bs : List (BitVec 8)) :
    (ptr + BitVec.ofNat 64 k) ↦ₛ (b :: bs) =
      (ptr + BitVec.ofNat 64 k) ↦₈ b ∗ (ptr + BitVec.ofNat 64 (k + 1)) ↦ₛ bs := by
  have hadd : ptr + BitVec.ofNat 64 k + 1#64 = ptr + BitVec.ofNat 64 (k + 1) := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp
  rw [pointsToBytes_cons, hadd]

private theorem pointsToBytes_cons_off (ptr : BitVec 64) (k : Nat) (hk1 : k + 1 < 2 ^ 64)
    (b : BitVec 8) (bs : List (BitVec 8)) (Q : SepProp) :
    (ptr + BitVec.ofNat 64 k) ↦₈ b ∗ ((ptr + BitVec.ofNat 64 (k + 1)) ↦ₛ bs ∗ Q) =
      (ptr + BitVec.ofNat 64 k) ↦ₛ (b :: bs) ∗ Q := by
  rw [← sepConj_assoc, ← pointsToBytes_split_off ptr k hk1 b bs]

private abbrev dv5PlJoinPre {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s : State) (bufRef slot ptr v_stk_2 : BitVec 64)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8)) : SepProp :=
  bufRef ↦₆₄ slot ∗ slot ↦₆₄ ptr ∗
    (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (b0 :: b1 :: bs2).length ∗
    (ptr ↦₈ b0 ∗ ((ptr + 1#64) ↦₈ b1 ∗ (ptr + 2#64) ↦ₛ bs2)) ∗
    A.pool lim st s ∗
    stackAt (s0.sp - 64#64) decodeVarintSlowStackX ∗ memRegion (s0.sp - 56#64) 40 ∗
    (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)

private abbrev dv5PlJoinPost {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 : State) (bufRef slot ptr : BitVec 64)
    (bs : List (BitVec 8)) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (decodeVarint2SpecX A lim).post (⟨bufRef, slot, ptr, bs⟩, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private abbrev dv5PlJoinPanic {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 : State) (bufRef slot ptr : BitVec 64)
    (bs : List (BitVec 8)) (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨ (decodeVarint2SpecX A lim).onPanic (⟨bufRef, slot, ptr, bs⟩, st) s0 sf ∗ R)

local macro "dv5_unfold_post" : tactic => `(tactic| (
  conv =>
    arg 5; ext sf P_f
    unfold dv5PlJoinPost
    simp only [decodeVarint2SpecX, stackAt_decodeVarint2X,
      sepExists_sepConj_left, sepExists_sepConj_right]
))

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

set_option maxHeartbeats 1600000 in
private theorem decodeVarint5_placed_join_none_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok (lsProg_515 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (st : M.σ) (s0 s : State)
    (bufRef slot ptr v_stk_2 : BitVec 64) (R : SepProp)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8))
    (hj : Dv5JoinAt s0 s slot ptr b0 b1 bs2 (blkPl_515).base)
    (hfits : FitsEnv M lim st (DecodeVarint2Env (b0 :: b1 :: bs2)))
    (hpre : VarintSlicePre (b0 :: b1 :: bs2))
    (hnone : decodeVarint (b0 :: b1 :: bs2) = none)
    (hcl_join : LibsignalCodeLoaded lsmpl s.mem) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr) s
      (dv5PlJoinPre A lim st s0 s bufRef slot ptr v_stk_2 b0 b1 bs2)
      (dv5PlJoinPost A lim st s0 bufRef slot ptr (b0 :: b1 :: bs2) R)
      (dv5PlJoinPanic A lim st s0 bufRef slot ptr (b0 :: b1 :: bs2) R) := by
  rcases hj with ⟨hpc_s, hrun_s, hsp_s, hsp_al_s, htr_s,
    hx1_s, hx8_s, hx9_s, hx10_s, hx11_s, hx29_s,
    hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hvregs_s⟩
  dsimp only [dv5PlJoinPre]
  have hfits_de := fitsEnv_decodeErrorFrom_of_dv2_none hnone hfits
  obtain ⟨b0', b1', b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
    hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre hpre hnone
  cases heq
  have hbit1 := getLsbD_7_beq_of_gt hb1
  have hbit2 := getLsbD_7_beq_of_gt hb2
  have hbit3 := getLsbD_7_beq_of_gt hb3
  have hbit4 := getLsbD_7_beq_of_gt hb4
  have hbit5 := getLsbD_7_beq_of_gt hb5
  have hbit6 := getLsbD_7_beq_of_gt hb6
  have hbit7 := getLsbD_7_beq_of_gt hb7
  have hbit8 := signExtend64_getLsbD_63_beq_of_gt hb8
  have hovf2 := ovf_byte2 hb0 hb1
  have hovf3 := ovf_byte3 hb0 hb1 hb2
  have hovf4 := ovf_byte4_zext hb0 hb1 hb2 hb3
  have hovf6 := ovf_byte6 hb4 hb5
  have hovf7 := ovf_byte7 hb4 hb5 hb6
  have hovf8 := ovf_byte8_zext hb4 hb5 hb6 hb7
  have hb9_ult := byte9_ult1_of_ge hb9
  have hb9_ule := byte9_ule_of_ge hb9
  apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_join
  conv =>
    arg 4
    rw [pointsToBytes_split_off ptr 2 (by decide),
      pointsToBytes_split_off ptr 3 (by decide),
      pointsToBytes_split_off ptr 4 (by decide),
      pointsToBytes_split_off ptr 5 (by decide),
      pointsToBytes_split_off ptr 6 (by decide),
      pointsToBytes_split_off ptr 7 (by decide),
      pointsToBytes_split_off ptr 8 (by decide),
      pointsToBytes_split_off ptr 9 (by decide)]
  wp_steps_sync_pool (lsmpl.base 261)
  simp only [State.setMem_setMem]
  apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr
    (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length))
    (by sep_focus)
  conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
  wp_reach
  intro hcl_err
  refine call_frame_budget_lscl
    (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
    (x := (s0.sp - 64#64, 0x8000000000000001#64, st))
    (φ := s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64 ∧
      FitsEnv M lim st DecodeErrorFromEnv)
    (ret_pc := (blkPl_515).base + 460#64) (lscl_of_cl hFromCall) hcl_err
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun_s])
    (by simp only [State.spAligned, arm64_norm, hsp_s] at hsp_al_s ⊢; exact hsp_al_s)
    (by simp only [arm64_norm])
    (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm, hsp_s]; rfl)
    ⟨rfl, by decide, hfits_de⟩
    (by sep_focus)
    ?_
  intro sm hpcm hrunm hspm hcsm _hcl_post
  simp only [CalleeSavedPreserved, arm64_norm, hsp_s,
    hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hvregs_s, hx29_s]
    at hspm hcsm
  rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
  apply SepWPp.of_sepWP_ret
  dv5_unfold_post
  conv =>
    arg 4
    simp only [decodeErrorFromBudgetSpecWithStack, memRegion_48_split,
      sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, htr_s, hsp_s]
  apply SepWP.exists_elim; intro evs
  apply SepWP.exists_elim; intro v_err
  wp_pull_pures
  have hevs_de : DecodeErrorFromEnv evs := by assumption
  have hevs_dv := dv2Env_of_decodeErrorFrom hnone hevs_de
  apply SepWP.fold (stackAt_errorHookX_entails_slowX s0.sp) (by sep_focus)
  conv =>
    arg 5; ext sf P_f
    rw [hnone]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  simp only [State.setMem_setMem]
  conv =>
    arg 4
    rw [pointsToBytes_cons_off ptr 9 (by decide),
      pointsToBytes_cons_off ptr 8 (by decide),
      pointsToBytes_cons_off ptr 7 (by decide),
      pointsToBytes_cons_off ptr 6 (by decide),
      pointsToBytes_cons_off ptr 5 (by decide),
      pointsToBytes_cons_off ptr 4 (by decide),
      pointsToBytes_cons_off ptr 3 (by decide),
      pointsToBytes_cons_off ptr 2 (by decide),
      pointsToBytes_cons_off ptr 1 (by decide),
      pointsToBytes_cons_zero ptr]
  wp_done

set_option maxHeartbeats 1200000 in
private theorem decodeVarint5_placed_join_2_to_5_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (st : M.σ) (s0 s : State)
    (bufRef slot ptr v_stk_2 : BitVec 64) (R : SepProp)
    (b0 b1 : BitVec 8) (bs2 : List (BitVec 8))
    (hj : Dv5JoinAt s0 s slot ptr b0 b1 bs2 (blkPl_515).base)
    (hb0 : ¬ b0 ≤ 0x7f#8)
    (hpre : VarintSlicePre (b0 :: b1 :: bs2))
    (h25 : b1 ≤ 0x7f#8 ∨ ∃ b2 bs3, bs2 = b2 :: bs3 ∧
      (b2 ≤ 0x7f#8 ∨ ∃ b3 bs4, bs3 = b3 :: bs4 ∧
        (b3 ≤ 0x7f#8 ∨ ∃ b4 bs5, bs4 = b4 :: bs5 ∧ b4 ≤ 0x7f#8))) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr) s
      (dv5PlJoinPre A lim st s0 s bufRef slot ptr v_stk_2 b0 b1 bs2)
      (dv5PlJoinPost A lim st s0 bufRef slot ptr (b0 :: b1 :: bs2) R)
      (dv5PlJoinPanic A lim st s0 bufRef slot ptr (b0 :: b1 :: bs2) R) := by
  rcases hj with ⟨hpc_s, hrun_s, hsp_s, hsp_al_s, htr_s,
    hx1_s, hx8_s, hx9_s, hx10_s, hx11_s, hx29_s,
    hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hvregs_s⟩
  dsimp only [dv5PlJoinPre]
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  apply SepWPp.of_sepWP_ret
  dv5_unfold_post
  by_cases hb1 : b1 ≤ 0x7f#8
  · have hbit1 := getLsbD_7_beq_of_le hb1
    have hd2 := decodeVarint_2 bs2 hb0 hb1
    have hevs_dv := dv2Env_nil_of_some hd2
    conv => arg 5; ext sf P_f; rw [hd2]; dsimp only; rw [sliceCursorAfter_of_eq (k := 2) rfl]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    conv =>
      arg 4
      rw [pointsToBytes_cons_off ptr 1 (by decide),
        pointsToBytes_cons_zero ptr, hpool_nil]
    wp_done
  · have hbit1 := getLsbD_7_beq_of_gt hb1
    have hovf2 := ovf_byte2 hb0 hb1
    obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) hpre (by simp)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        hb0, hb1, not_false_eq_true, and_self])
    conv => arg 4; rw [pointsToBytes_split_off ptr 2 (by decide)]
    by_cases hb2 : b2 ≤ 0x7f#8
    · have hbit2 := getLsbD_7_beq_of_le hb2
      have hd3 := decodeVarint_3 bs3 hb0 hb1 hb2
      have hevs_dv := dv2Env_nil_of_some hd3
      conv => arg 5; ext sf P_f; rw [hd3]; dsimp only; rw [sliceCursorAfter_of_eq (k := 3) rfl]
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      conv =>
        arg 4
        rw [pointsToBytes_cons_off ptr 2 (by decide),
          pointsToBytes_cons_off ptr 1 (by decide),
          pointsToBytes_cons_zero ptr, hpool_nil]
      wp_done
    · have hbit2 := getLsbD_7_beq_of_gt hb2
      have hovf3 := ovf_byte3 hb0 hb1 hb2
      obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) hpre (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          hb0, hb1, hb2, not_false_eq_true, and_self])
      conv => arg 4; rw [pointsToBytes_split_off ptr 3 (by decide)]
      by_cases hb3 : b3 ≤ 0x7f#8
      · have hbit3 := getLsbD_7_beq_of_le hb3
        have hd4 := decodeVarint_4 bs4 hb0 hb1 hb2 hb3
        have hevs_dv := dv2Env_nil_of_some hd4
        conv => arg 5; ext sf P_f; rw [hd4]; dsimp only; rw [sliceCursorAfter_of_eq (k := 4) rfl]
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        conv =>
          arg 4
          rw [pointsToBytes_cons_off ptr 3 (by decide),
            pointsToBytes_cons_off ptr 2 (by decide),
            pointsToBytes_cons_off ptr 1 (by decide),
            pointsToBytes_cons_zero ptr, hpool_nil]
        wp_done
      · have hbit3 := getLsbD_7_beq_of_gt hb3
        have hovf4 := ovf_byte4_zext hb0 hb1 hb2 hb3
        obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
        conv => arg 4; rw [pointsToBytes_split_off ptr 4 (by decide)]
        by_cases hb4 : b4 ≤ 0x7f#8
        · have hbit4 := getLsbD_7_beq_of_le hb4
          have hd5 := decodeVarint_5 bs5 hb0 hb1 hb2 hb3 hb4
          have hevs_dv := dv2Env_nil_of_some hd5
          conv => arg 5; ext sf P_f; rw [hd5]; dsimp only; rw [sliceCursorAfter_of_eq (k := 5) rfl]
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          conv =>
            arg 4
            rw [pointsToBytes_cons_off ptr 4 (by decide),
              pointsToBytes_cons_off ptr 3 (by decide),
              pointsToBytes_cons_off ptr 2 (by decide),
              pointsToBytes_cons_off ptr 1 (by decide),
              pointsToBytes_cons_zero ptr, hpool_nil]
          wp_done
        · exfalso
          rcases h25 with h1 | ⟨b2', bs3', hcons2, h2 | ⟨b3', bs4', hcons3, h3 | ⟨b4', bs5', hcons4, h4⟩⟩⟩
          · exact hb1 h1
          · cases hcons2; exact hb2 h2
          · cases hcons2; cases hcons3; exact hb3 h3
          · cases hcons2; cases hcons3; cases hcons4; exact hb4 h4

set_option maxHeartbeats 1200000 in
private theorem decodeVarint5_placed_join_6_to_10_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (st : M.σ) (s0 s : State)
    (bufRef slot ptr v_stk_2 : BitVec 64) (R : SepProp)
    (b0 b1 b2 b3 b4 : BitVec 8) (bs5 : List (BitVec 8))
    (hj : Dv5JoinAt s0 s slot ptr b0 b1 (b2 :: b3 :: b4 :: bs5) (blkPl_515).base)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8)
    (hpre : VarintSlicePre (b0 :: b1 :: b2 :: b3 :: b4 :: bs5))
    (hnone : ¬ decodeVarint (b0 :: b1 :: b2 :: b3 :: b4 :: bs5) = none) :
    SepWPp (lsProg_515 H) (s0.readReg64 Reg.lr) s
      (dv5PlJoinPre A lim st s0 s bufRef slot ptr v_stk_2 b0 b1 (b2 :: b3 :: b4 :: bs5))
      (dv5PlJoinPost A lim st s0 bufRef slot ptr (b0 :: b1 :: b2 :: b3 :: b4 :: bs5) R)
      (dv5PlJoinPanic A lim st s0 bufRef slot ptr (b0 :: b1 :: b2 :: b3 :: b4 :: bs5) R) := by
  rcases hj with ⟨hpc_s, hrun_s, hsp_s, hsp_al_s, htr_s,
    hx1_s, hx8_s, hx9_s, hx10_s, hx11_s, hx29_s,
    hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hvregs_s⟩
  dsimp only [dv5PlJoinPre]
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  apply SepWPp.of_sepWP_ret
  dv5_unfold_post
  have hbit1 := getLsbD_7_beq_of_gt hb1
  have hovf2 := ovf_byte2 hb0 hb1
  have hbit2 := getLsbD_7_beq_of_gt hb2
  have hovf3 := ovf_byte3 hb0 hb1 hb2
  have hbit3 := getLsbD_7_beq_of_gt hb3
  have hovf4 := ovf_byte4_zext hb0 hb1 hb2 hb3
  have hbit4 := getLsbD_7_beq_of_gt hb4
  obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) hpre (by simp)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
  conv =>
    arg 4
    rw [pointsToBytes_split_off ptr 2 (by decide),
      pointsToBytes_split_off ptr 3 (by decide),
      pointsToBytes_split_off ptr 4 (by decide),
      pointsToBytes_split_off ptr 5 (by decide)]
  by_cases hb5 : b5 ≤ 0x7f#8
  · have hbit5 := getLsbD_7_beq_of_le hb5
    have hd6 := decodeVarint_6 bs6 hb0 hb1 hb2 hb3 hb4 hb5
    have hevs_dv := dv2Env_nil_of_some hd6
    conv => arg 5; ext sf P_f; rw [hd6]; dsimp only; rw [sliceCursorAfter_of_eq (k := 6) rfl]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    conv =>
      arg 4
      rw [pointsToBytes_cons_off ptr 5 (by decide),
        pointsToBytes_cons_off ptr 4 (by decide),
        pointsToBytes_cons_off ptr 3 (by decide),
        pointsToBytes_cons_off ptr 2 (by decide),
        pointsToBytes_cons_off ptr 1 (by decide),
        pointsToBytes_cons_zero ptr, hpool_nil]
    wp_done
  · have hbit5 := getLsbD_7_beq_of_gt hb5
    have hovf6 := ovf_byte6 hb4 hb5
    obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) hpre
      (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
        and_self])
    conv => arg 4; rw [pointsToBytes_split_off ptr 6 (by decide)]
    by_cases hb6 : b6 ≤ 0x7f#8
    · have hbit6 := getLsbD_7_beq_of_le hb6
      have hd7 := decodeVarint_7 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6
      have hevs_dv := dv2Env_nil_of_some hd7
      conv => arg 5; ext sf P_f; rw [hd7]; dsimp only; rw [sliceCursorAfter_of_eq (k := 7) rfl]
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      conv =>
        arg 4
        rw [pointsToBytes_cons_off ptr 6 (by decide),
          pointsToBytes_cons_off ptr 5 (by decide),
          pointsToBytes_cons_off ptr 4 (by decide),
          pointsToBytes_cons_off ptr 3 (by decide),
          pointsToBytes_cons_off ptr 2 (by decide),
          pointsToBytes_cons_off ptr 1 (by decide),
          pointsToBytes_cons_zero ptr, hpool_nil]
      wp_done
    · have hbit6 := getLsbD_7_beq_of_gt hb6
      have hovf7 := ovf_byte7 hb4 hb5 hb6
      obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
        (pre := [b0, b1, b2, b3, b4, b5, b6]) hpre (by simp)
        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
      conv => arg 4; rw [pointsToBytes_split_off ptr 7 (by decide)]
      by_cases hb7 : b7 ≤ 0x7f#8
      · have hbit7 := getLsbD_7_beq_of_le hb7
        have hd8 := decodeVarint_8 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
        have hevs_dv := dv2Env_nil_of_some hd8
        conv => arg 5; ext sf P_f; rw [hd8]; dsimp only; rw [sliceCursorAfter_of_eq (k := 8) rfl]
        wp_steps_sync_pool (s0.readReg64 Reg.lr)
        simp only [State.setMem_setMem]
        conv =>
          arg 4
          rw [pointsToBytes_cons_off ptr 7 (by decide),
            pointsToBytes_cons_off ptr 6 (by decide),
            pointsToBytes_cons_off ptr 5 (by decide),
            pointsToBytes_cons_off ptr 4 (by decide),
            pointsToBytes_cons_off ptr 3 (by decide),
            pointsToBytes_cons_off ptr 2 (by decide),
            pointsToBytes_cons_off ptr 1 (by decide),
            pointsToBytes_cons_zero ptr, hpool_nil]
        wp_done
      · have hbit7 := getLsbD_7_beq_of_gt hb7
        have hovf8 := ovf_byte8_zext hb4 hb5 hb6 hb7
        obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
          (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) hpre (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
            forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
            and_self])
        conv => arg 4; rw [pointsToBytes_split_off ptr 8 (by decide)]
        by_cases hb8 : b8 ≤ 0x7f#8
        · have hbit8 := signExtend64_getLsbD_63_beq_of_le hb8
          have hd9 := decodeVarint_9 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8
          have hevs_dv := dv2Env_nil_of_some hd9
          conv => arg 5; ext sf P_f; rw [hd9]; dsimp only; rw [sliceCursorAfter_of_eq (k := 9) rfl]
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          conv =>
            arg 4
            rw [pointsToBytes_cons_off ptr 8 (by decide),
              pointsToBytes_cons_off ptr 7 (by decide),
              pointsToBytes_cons_off ptr 6 (by decide),
              pointsToBytes_cons_off ptr 5 (by decide),
              pointsToBytes_cons_off ptr 4 (by decide),
              pointsToBytes_cons_off ptr 3 (by decide),
              pointsToBytes_cons_off ptr 2 (by decide),
              pointsToBytes_cons_off ptr 1 (by decide),
              pointsToBytes_cons_zero ptr, hpool_nil]
          wp_done
        · have hbit8 := signExtend64_getLsbD_63_beq_of_gt hb8
          obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
            (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) hpre (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
              forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, not_false_eq_true,
              and_self])
          have hb9 : ¬ 2#8 ≤ b9 := by
            intro hge
            apply hnone
            rw [decodeVarint]; iterate 10 rw [decodeVarintAux]
            by_cases hb9_le : b9 ≤ 0x7f#8 <;>
              simp [toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4, hb5,
                hb6, hb7, hb8, hb9_le, hge]
          have hb9_ult := byte9_ult1_of_lt hb9
          have hb9_ule := byte9_ule_of_lt hb9
          have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
          conv => arg 4; rw [pointsToBytes_split_off ptr 9 (by decide)]
          have hd10 := decodeVarint_10 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
          have hevs_dv := dv2Env_nil_of_some hd10
          conv => arg 5; ext sf P_f; rw [hd10]; dsimp only; rw [sliceCursorAfter_of_eq (k := 10) rfl]
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          conv =>
            arg 4
            rw [pointsToBytes_cons_off ptr 9 (by decide),
              pointsToBytes_cons_off ptr 8 (by decide),
              pointsToBytes_cons_off ptr 7 (by decide),
              pointsToBytes_cons_off ptr 6 (by decide),
              pointsToBytes_cons_off ptr 5 (by decide),
              pointsToBytes_cons_off ptr 4 (by decide),
              pointsToBytes_cons_off ptr 3 (by decide),
              pointsToBytes_cons_off ptr 2 (by decide),
              pointsToBytes_cons_off ptr 1 (by decide),
              pointsToBytes_cons_zero ptr, hpool_nil]
          wp_done

/-! ## Top-Level Verification of `decode_varint::<&mut &[u8]> [local#4]` (Block `515`) -/

set_option maxHeartbeats 1200000 in
theorem decodeVarint5_placed_ok_of_contracts_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim))) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) := by
  have hFromCall : subroutine_ok (lsProg_515 H) (lsmpl.base 261)
      (withLsCl lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)) :=
    ls_subroutine_ok_cl_of_block (callerProg := lsProg_515 H) hFrom
  have hSlowCall : subroutine_ok (lsProg_515 H) (lsmpl.base 293)
      (withLsCl lsmpl (decodeVarintSlowSpecX A lim)) :=
    ls_subroutine_ok_cl_of_block (callerProg := lsProg_515 H) hSlow
  clear hFrom hSlow
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarint2SpecX
    simp only [sliceCursorAt, stackAt_decodeVarint2X,
      sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨bufRef, slot, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_lt : bs.length < 2 ^ 63 := by assumption
  have hx0_slot : s0.readReg64 (Reg.gpr 0#5) = bufRef := by assumption
  have hfits : FitsEnv M lim st (DecodeVarint2Env bs) := by assumption
  have hpool_nil : A.pool lim st = A.pool lim (M.stepEvents ([] : List AllocEvent) st) := rfl
  have hjoin_dispatch : ∀ (st' : M.σ) (s0' s' : State)
      (bufRef' slot' ptr' v_stk_2' : BitVec 64) (R' : SepProp)
      (b0' b1' : BitVec 8) (bs2' : List (BitVec 8)),
      Dv5JoinAt s0' s' slot' ptr' b0' b1' bs2' (blkPl_515).base →
      FitsEnv M lim st' (DecodeVarint2Env (b0' :: b1' :: bs2')) →
      ¬ b0' ≤ 0x7f#8 →
      VarintSlicePre (b0' :: b1' :: bs2') →
      LibsignalCodeLoaded lsmpl s'.mem →
      SepWPp (lsProg_515 H) (s0'.readReg64 Reg.lr) s'
        (dv5PlJoinPre A lim st' s0' s' bufRef' slot' ptr' v_stk_2' b0' b1' bs2')
        (dv5PlJoinPost A lim st' s0' bufRef' slot' ptr' (b0' :: b1' :: bs2') R')
        (dv5PlJoinPanic A lim st' s0' bufRef' slot' ptr' (b0' :: b1' :: bs2') R') := by
    intro st' s0' s' bufRef' slot' ptr' v_stk_2' R' b0' b1' bs2' hj hfits' hb0' hpre' hcl_join
    by_cases hnone : decodeVarint (b0' :: b1' :: bs2') = none
    · exact decodeVarint5_placed_join_none_x hFromCall st' s0' s' bufRef' slot' ptr' v_stk_2' R'
        b0' b1' bs2' hj hfits' hpre' hnone hcl_join
    · by_cases h25 : b1' ≤ 0x7f#8 ∨ ∃ b2 bs3, bs2' = b2 :: bs3 ∧
          (b2 ≤ 0x7f#8 ∨ ∃ b3 bs4, bs3 = b3 :: bs4 ∧
            (b3 ≤ 0x7f#8 ∨ ∃ b4 bs5, bs4 = b4 :: bs5 ∧ b4 ≤ 0x7f#8))
      · exact decodeVarint5_placed_join_2_to_5_x st' s0' s' bufRef' slot' ptr' v_stk_2' R'
          b0' b1' bs2' hj hb0' hpre' h25
      · have hb1 : ¬ b1' ≤ 0x7f#8 := fun h => h25 (Or.inl h)
        obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0', b1']) hpre' (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0', hb1, not_false_eq_true, and_self])
        have hb2 : ¬ b2 ≤ 0x7f#8 := fun h => h25 (Or.inr ⟨b2, bs3, rfl, Or.inl h⟩)
        obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0', b1', b2]) hpre' (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0', hb1, hb2, not_false_eq_true, and_self])
        have hb3 : ¬ b3 ≤ 0x7f#8 :=
          fun h => h25 (Or.inr ⟨b2, b3 :: bs4, rfl, Or.inr ⟨b3, bs4, rfl, Or.inl h⟩⟩)
        obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0', b1', b2, b3]) hpre' (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            hb0', hb1, hb2, hb3, not_false_eq_true, and_self])
        have hb4 : ¬ b4 ≤ 0x7f#8 := fun h =>
          h25 (Or.inr ⟨b2, b3 :: b4 :: bs5, rfl, Or.inr ⟨b3, b4 :: bs5, rfl, Or.inr ⟨b4, bs5, rfl, h⟩⟩⟩)
        exact decodeVarint5_placed_join_6_to_10_x st' s0' s' bufRef' slot' ptr' v_stk_2' R'
          b0' b1' b2 b3 b4 bs5 hj hb0' hb1 hb2 hb3 hb4 hpre' hnone
  unfold dv5PlJoinPost dv5PlJoinPanic decodeVarint2SpecX at hjoin_dispatch
  simp only [stackAt_decodeVarint2X, sepExists_sepConj_left, sepExists_sepConj_right] at hjoin_dispatch
  cases bs with
  | nil =>
    have hd_nil : decodeVarint ([] : List (BitVec 8)) = none := rfl
    have hfits_de := fitsEnv_decodeErrorFrom_of_dv2_none hd_nil hfits
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl0
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_pair_entails_memRegion16 slot ptr (BitVec.ofNat 64 [].length)) (by sep_focus)
    conv => arg 4; rw [stackAt_slowX_eq_errorHookX (s0.sp - 64#64)]
    wp_reach
    intro hcl1
    refine call_frame_budget_lscl
      (spec := decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)
      (x := (s0.sp - 64#64, 0x8000000000000001#64, st))
      (φ := s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64 ∧
        FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_515).base + 460#64) (lscl_of_cl hFromCall) hcl1
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
    dv5_unfold_post
    conv =>
      arg 4
      simp only [decodeErrorFromBudgetSpecWithStack, memRegion_48_split,
        sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro v_err
    wp_pull_pures
    have hevs_de : DecodeErrorFromEnv evs := by assumption
    have hevs_dv := dv2Env_of_decodeErrorFrom hd_nil hevs_de
    apply SepWP.fold (stackAt_errorHookX_entails_slowX s0.sp) (by sep_focus)
    conv => arg 5; ext sf P_f; rw [hd_nil]
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    wp_done
  | cons b0 bs1 =>
    have hcbz := cbz_len_cons_false hlen_lt
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := signExtend64_getLsbD_63_beq_of_le hb0
      have hd1 := decodeVarint_1 bs1 hb0
      have hevs_dv := dv2Env_nil_of_some hd1
      apply SepWPp.of_sepWP_ret
      dv5_unfold_post
      conv => arg 5; ext sf P_f; rw [hd1]; dsimp only; rw [sliceCursorAfter_of_eq (k := 1) rfl]
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_sync_pool (s0.readReg64 Reg.lr)
      simp only [State.setMem_setMem]
      conv => arg 4; rw [pointsToBytes_cons_zero ptr, hpool_nil]
      wp_done
    · have hbit0 := signExtend64_getLsbD_63_beq_of_gt hb0
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 64#64) hcl0
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps_sync_pool ((blkPl_515).base + 64#64)
      simp only [State.setMem_setMem]
      wp_reach
      intro hcl1
      by_cases hpre_sl : VarintSlicePre (b0 :: bs1)
      · obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) hpre_sl (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        by_cases h11 : 11 ≤ (b0 :: b1 :: bs2).length
        · have hhi := ult_10_of_ge_11 h11 hlen_lt
          apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 88#64) hcl1
          conv => arg 4; rw [pointsToBytes_split_off ptr 1 (by decide)]
          wp_steps_sync_pool ((blkPl_515).base + 88#64)
          simp only [State.setMem_setMem]
          wp_reach
          intro hcl2
          refine SepWPp.congr_pre (P' := dv5PlJoinPre A lim st s0 _ bufRef slot ptr v_stk_2 b0 b1 bs2)
            (by dsimp only [dv5PlJoinPre]; (try simp only [arm64_norm]); sep_ac_rfl) ?_
          conv => arg 5; ext sf P_f; simp only [sepExists_sepConj_left]
          refine hjoin_dispatch st s0 _ bufRef slot ptr v_stk_2 R b0 b1 bs2 ?_ hfits hb0 hpre_sl hcl2
          refine ⟨by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm, hrun],
            by simp [wp_norm, arm64_norm],
            by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align,
            by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm],
            by simp [wp_norm, arm64_norm]⟩
        · have hpre_cases := hpre_sl
          rcases hpre_cases with h11' | ⟨hne, hlast⟩
          · exact (h11 h11').elim
          · have hhi := ult_10_of_lt_11 h11 hlen_lt
            have hbit_last := getLsbD_7_beq_of_le hlast
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 84#64) hcl1
            conv =>
              arg 4
              rw [pointsToBytes_cons_zero ptr, pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne hlen_lt]
            wp_steps_sync_pool ((blkPl_515).base + 84#64)
            simp only [State.setMem_setMem]
            apply SepWP.fold (Entails.of_eq (pointsToBytes_split_last ptr (b0 :: b1 :: bs2) hne hlen_lt).symm)
              (by sep_focus)
            conv =>
              arg 4
              rw [pointsToBytes_cons, pointsToBytes_split_off ptr 1 (by decide)]
            wp_reach
            intro hcl2
            apply SepWPp.of_sepWP_lscl (mid := (blkPl_515).base + 88#64) hcl2
            wp_steps_sync_pool ((blkPl_515).base + 88#64)
            simp only [State.setMem_setMem]
            wp_reach
            intro hcl3
            refine SepWPp.congr_pre (P' := dv5PlJoinPre A lim st s0 _ bufRef slot ptr v_stk_2 b0 b1 bs2)
              (by dsimp only [dv5PlJoinPre]; (try simp only [arm64_norm]); sep_ac_rfl) ?_
            conv => arg 5; ext sf P_f; simp only [sepExists_sepConj_left]
            refine hjoin_dispatch st s0 _ bufRef slot ptr v_stk_2 R b0 b1 bs2 ?_ hfits hb0 hpre_sl hcl3
            refine ⟨by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm, hrun],
              by simp [wp_norm, arm64_norm],
              by simpa [State.spAligned, wp_norm, arm64_norm] using hsp_align,
              by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm],
              by simp [wp_norm, arm64_norm]⟩
      · have h11 : ¬ 11 ≤ (b0 :: bs1).length := fun h => hpre_sl (Or.inl h)
        have hne : b0 :: bs1 ≠ [] := List.cons_ne_nil b0 bs1
        have hlast : ¬ (b0 :: bs1).getLast hne ≤ 0x7f#8 := fun h => hpre_sl (Or.inr ⟨hne, h⟩)
        have hhi := ult_10_of_lt_11 h11 hlen_lt
        have hbit_last := getLsbD_7_beq_of_gt hlast
        have hfits_slw := fitsEnv_varintSlow_of_dv2 hfits
        apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 293) hcl1
        conv =>
          arg 4
          rw [pointsToBytes_cons_zero ptr, pointsToBytes_split_last ptr (b0 :: bs1) hne hlen_lt]
        wp_steps_sync_pool (lsmpl.base 293)
        simp only [State.setMem_setMem]
        apply SepWP.fold (Entails.of_eq (pointsToBytes_split_last ptr (b0 :: bs1) hne hlen_lt).symm)
          (by sep_focus)
        wp_reach
        intro hcl_slow
        refine call_frame_budget_lscl (spec := decodeVarintSlowSpecX A lim)
          (x := (⟨bufRef, slot, ptr, b0 :: bs1⟩, st))
          (φ := bufRef = bufRef ∧ (b0 :: bs1).length < 2 ^ 63 ∧
            FitsEnv M lim st (DecodeVarintSlowEnv (b0 :: bs1)))
          (ret_pc := (blkPl_515).base + 484#64) (lscl_of_cl hSlowCall) hcl_slow
          (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
          (by simp only [arm64_norm])
          (by simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, arm64_norm, hx0_slot]; rfl)
          ⟨rfl, hlen_lt, hfits_slw⟩
          (by simp only [sliceCursorAt]; sep_focus)
          ?_
        intro sm hpcm hrunm hspm hcsm _hcl_post
        simp only [CalleeSavedPreserved, arm64_norm] at hcsm
        rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
        apply SepWPp.of_sepWP_ret
        cases hd : decodeVarint (b0 :: bs1) with
        | none =>
          conv => arg 5; ext sf P_f; dsimp only
          conv =>
            arg 4
            simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
          apply SepWP.exists_elim; intro evs
          wp_pull_pures
          have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
          have hevs_dv := dv2Env_of_varintSlow hevs_slw
          have htr_sm : sm.trace = s0.trace :=
            ‹sm.trace = _›.trans (by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved])
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          wp_done
        | some p =>
          rcases p with ⟨v, rest⟩
          conv => arg 5; ext sf P_f; dsimp only
          conv =>
            arg 4
            simp only [decodeVarintSlowSpecX, decodeVarintSlowSpecGen, hd,
              sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, arm64_norm]
          apply SepWP.exists_elim; intro evs
          wp_pull_pures
          have hevs_slw : DecodeVarintSlowEnv (b0 :: bs1) evs := by assumption
          have hevs_dv := dv2Env_of_varintSlow hevs_slw
          have htr_sm : sm.trace = s0.trace :=
            ‹sm.trace = _›.trans (by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved])
          wp_steps_sync_pool (s0.readReg64 Reg.lr)
          simp only [State.setMem_setMem]
          wp_done

/-- `withLsCodeLoaded pl (decodeErrorFromBudgetSpecWithStack M A lim s1)` entails the same spec
at any larger stack budget `s2 ≤ 2 ^ 64`. -/
theorem decodeErrorFromBudgetSpecWithStack_lscl_le {pl : Obj.MultiPlacement} {P : Program}
    {addr : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {s1 s2 : Nat}
    (h : subroutine_ok P addr
      (withLsCodeLoaded pl (decodeErrorFromBudgetSpecWithStack M A lim s1)))
    (hle : s1 ≤ s2 := by decide) (hmax : s2 ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr
      (withLsCodeLoaded pl (decodeErrorFromBudgetSpecWithStack M A lim s2)) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded pl (decodeErrorFromBudgetSpecWithStack M A lim s1)).pre (k, w, st) s0 ∗
        (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) := by
    dsimp only [withLsCodeLoaded, decodeErrorFromBudgetSpecWithStack] at hpre ⊢
    rw [hsplit] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (k, w, st) (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, decodeErrorFromBudgetSpecWithStack] at hpost ⊢
    rw [hsplit]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

alias decodeErrorFromSpecWithStack_lscl_le := decodeErrorFromBudgetSpecWithStack_lscl_le

theorem dv5_decodeErrorFrom_placed_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hAlloc : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (blkPl_261).base
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)) :=
  decodeErrorFromBudgetSpecWithStack_lscl_le
    (s1 := decodeErrorHookStackW)
    (s2 := decodeErrorHookStackX)
    (decodeErrorFrom_placed_okW hAlloc)

theorem dv5_decodeVarintSlow_placed_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hAlloc : AllocContractsPlaced M A lim H) :
    subroutine_ok ((blkPC_293).rebase (blkPl_293).base H) (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)) :=
  decodeVarintSlowGen_lscl_ok_of_session2
    (decode_varint_slow_placed_ok_with_stack
      (errStack := decodeErrorHookStackX) (by decide)
      (ls_subroutine_ok_cl_of_block
        (callerProg := (blkPC_293).rebase (blkPl_293).base H)
        (dv5_decodeErrorFrom_placed_of_alloc hAlloc)))

/-- Budget-threaded `decodeVarint2SpecX` on Block `515` (`lsProg_515 H`) from `AllocContractsPlaced`. -/
theorem decodeVarint5_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hAlloc : AllocContractsPlaced M A lim H) :
    subroutine_ok (lsProg_515 H) (blkPl_515).base
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) :=
  decodeVarint5_placed_ok_of_contracts_x
    (dv5_decodeErrorFrom_placed_of_alloc hAlloc)
    (dv5_decodeVarintSlow_placed_of_alloc hAlloc)

theorem decodeVarint5_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i H]
    (hAlloc : AllocContractsPlaced M A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim)) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg) (decodeVarint5_placed_ok hAlloc) hi

theorem decodeVarint5_placed_ok_ext_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    DecodeVarint5PlacedOkExtX A lim ext :=
  decodeVarint5_placed_ok_cl (callerProg := lsProg_518 ext) hAlloc

alias bm6_decodeVarint5_placed_of_alloc := decodeVarint5_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
