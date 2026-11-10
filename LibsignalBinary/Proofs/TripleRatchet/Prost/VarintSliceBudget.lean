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
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSlice
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Verification of `prost::encoding::varint::decode_varint_slice`

Relocatable `RustCliAllocBudget`-threaded verification of `<DecodeError as From<DecodeErrorKind>>::from`
(block 261) and `prost::encoding::varint::decode_varint_slice` (block 76).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (subroutine_ok_allocNoOom_externWithStack_of_hookSat)
open LibsignalBinary.Heap.SpecBudget
  (DecodeErrorFromEnv decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement lsmpl
   blkPC_76 blkPl_76 blkPC_261 blkPl_261
   lsRustAllocSym lsRustNoAllocShimSym ls_externAt?_of_mem ls_hook_ok_of_mem
   ls_subroutine_ok_cl_of_plain lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.RustHeap (LayoutOk allocHookStack)
open CryptoVerification.LibsignalProtoCodec (decodeVarint decodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet
  (KindNoHeap decodeErrorAtStackLen decodeErrorHookStack)
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom
  (cells6_entails_memRegion48 decodeErrorWith_zero_entails memRegion_40_cells memRegion_72_cells
   stackAt_decodeErrorFrom)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SepWPp.call_frame_lscl SepWPp.of_sepWP_lscl VarintSlicePre
   byte9_ule_of_ge byte9_ule_of_lt decodeErrorHookStackX decodeVarint_eq_none_of_pre
   eq_ofNat_of_toNat_eq exists_cons_of_all_gt hw_part01_eq hw_part0_eq
   memRegion_24_cells memRegion_48_split
   ovf_byte2 ovf_byte3 ovf_byte6 ovf_byte7 ovf_byte10
   part0_2 part0_3 part0_4 part1_2 part1_3 part1_4
   pointsTo64_entails_memRegion8 pointsToBytes_split_last stackAt_decodeVarintSliceGen
   toNat_le_0x7f_iff two_le_toNat_iff
   ule_11_of_ge ule_11_of_lt
   vAcc1 vAcc2 vAcc3 vAcc4 vAcc5 vAcc6 vAcc7 vAcc8 vAcc9 vAcc10
   vAcc1_eq vAcc2_eq vAcc3_eq vAcc4_eq vAcc5_eq vAcc6_eq vAcc7_eq vAcc8_eq vAcc9_eq
   varintSliceResultAt varintSliceResultAt_1 varintSliceResultAt_2 varintSliceResultAt_3
   varintSliceResultAt_4 varintSliceResultAt_5 varintSliceResultAt_6 varintSliceResultAt_7
   varintSliceResultAt_8 varintSliceResultAt_9 varintSliceResultAt_10)
open CryptoVerification.LibsignalTripleRatchet.Prost.VarintSliceBits
  (getLsbD_7_beq_of_gt getLsbD_7_beq_of_le ovf_byte4_zext ovf_byte8_zext
   signExtend64_getLsbD_63_beq_of_gt signExtend64_getLsbD_63_beq_of_le)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (decodeErrorFromWithStack_of_decodeErrorFrom)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv DecodeVarintSlicePlacedOk DecodeVarintSlicePlacedOkX
   decodeVarintSliceEvents decodeVarintSliceSpec decodeVarintSliceSpecGen decodeVarintSliceSpecX)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

open Lean Elab Tactic Meta in
local elab "wp_ret8_bv_bits " retStx:term:max ppSpace targetVal:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let addr ← elabTerm (← `($retStx + 8#64)) none
    let rhs ← elabTerm targetVal none
    let ty ← instantiateMVars (← g.getType)
    let pExpr := ty.getArg! 3
    let some sub := pExpr.find? fun e =>
        e.isAppOfArity ``Arm64.pointsTo64 2 && e.getArg! 0 == addr
      | throwError "wp_ret8_bv_bits: no (ret + 8#64) ↦₆₄ _ found in spatial context"
    let rhsCell ← mkAppM ``Arm64.pointsTo64 #[addr, rhs]
    let cellEqTy ← mkEq sub rhsCell
    let prfMVar ← mkFreshExprMVar cellEqTy
    let gs ← getGoals
    let mut toClear : Array FVarId := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let u := decl.userName
        if u != `b0 && u != `b1 && u != `b2 && u != `b3 && u != `b4 &&
           u != `b5 && u != `b6 && u != `b7 && u != `b8 && u != `b9 &&
           u != `hb0 && u != `hb1 && u != `hb2 && u != `hb3 && u != `hb4 &&
           u != `hb5 && u != `hb6 && u != `hb7 && u != `hb8 && u != `hb9 &&
           u != `ret then
          toClear := toClear.push decl.fvarId
    let mId ← prfMVar.mvarId!.tryClearMany toClear
    setGoals [mId]
    let hb0 := mkIdent `hb0
    let hb1 := mkIdent `hb1
    let hb2 := mkIdent `hb2
    let hb3 := mkIdent `hb3
    let hb4 := mkIdent `hb4
    let hb5 := mkIdent `hb5
    let hb6 := mkIdent `hb6
    let hb7 := mkIdent `hb7
    let hb8 := mkIdent `hb8
    evalTactic (← `(tactic| (
      apply pointsTo64_congr_val
      first
      | (rw [hw_part01_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
               $hb4:ident $hb5:ident $hb6:ident $hb7:ident
         try (rw [vAcc10]; refine congrArg₂ (· ||| ·) ?_ (by clear $hb8:ident; bv_bits))
         rw [vAcc9_eq]
         bv_bits)
      | (rw [hw_part0_eq $hb0:ident $hb1:ident $hb2:ident $hb3:ident]
         clear $hb0:ident $hb1:ident $hb2:ident $hb3:ident
         simp only [vAcc8_eq, vAcc7_eq, vAcc6_eq, vAcc5_eq, part1_4, part1_3, part1_2]
         bv_bits)
      | (simp only [vAcc4_eq, vAcc3_eq, vAcc2_eq, vAcc1_eq, part0_4, part0_3, part0_2]
         bv_bits))))
    setGoals gs
    let g' ← g.assert `hret8_val cellEqTy (← instantiateMVars prfMVar)
    let (_, g'') ← g'.intro1P
    replaceMainGoal [g'']
    let hId := mkIdent `hret8_val
    evalTactic (← `(tactic| (rw [$hId:ident]; clear $hId:ident)))

local macro "wp_reach" : tactic =>
  `(tactic| apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, *]))

private theorem with_wp_state {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (k : (s' : State) → s' = s → SepWP prog target s P post) :
    SepWP prog target s P post := k s rfl

private theorem pool_to_setMem {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s0 s1 : State) (m : Memory)
    (h : VmPreserved (s0.setMem m) (s1.setMem m)) :
    A.pool lim st (s1.setMem m) = A.pool lim st (s0.setMem m) :=
  A.pool_of_vmPreserved h

/-! ## Relocatable `<DecodeError as From<DecodeErrorKind>>::from` (block 261) -/

private def shimVmSpec : Spec Unit where
  pre := fun _ _ => ⌜True⌝ ∗ emp
  post := fun _ s0 sf => ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ emp

private theorem shimVm_of_sessionShimBudget {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionShimBudgetSpec) :
    subroutine_ok prog addr shimVmSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => ?_)
  · dsimp only [shimVmSpec, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hp ⊢
    simpa only [pure_true, emp_sepConj] using hp
  · dsimp only [shimVmSpec, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hq ⊢
    simp only [sepConj_assoc, emp_sepConj, satisfies_pure_sepConj] at hq ⊢
    exact ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩

/-- Relocatable `<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from`
(Block `261`, `0x4ada0`) meets `decodeErrorFromBudgetSpec M A lim`. -/
theorem decode_error_from_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpec M A lim) := by
  simp only [decodeErrorFromBudgetSpec, stackAt_decodeErrorFrom]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (lsρ lsRustNoAllocShimSym) shimVmSpec :=
    shimVm_of_sessionShimBudget (ls_hook_ok_of_mem hshim)
  have halloc' : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc
      (ls_externAt?_of_mem (sym := lsRustAllocSym))
  simp only [rustCliAllocNoOomExternSpecWithStack,
    _root_.LibsignalBinary.Heap.rustCliAllocNoOomSpec] at halloc'
  clear hshim halloc
  wp_init x s0
  rcases x with ⟨k, w, st⟩
  dsimp only at *
  have hkw : KindNoHeap w := by assumption
  have hfits_env : FitsEnv M lim st DecodeErrorFromEnv := by assumption
  have hfits72 : FitsEvents M lim st (rustAllocEvents 72 8) := hfits_env _ rfl
  obtain ⟨henf, hphys72, hva72⟩ := hfits72.1.2
  have hpow8 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : RustLayoutOk 72 8 := ⟨⟨by decide, hpow8, by decide⟩, by decide⟩
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  apply with_wp_state; intro s_pre_shim hs_pre
  wp_call hshim' ()
  apply with_wp_state; intro sf_shim hsf_shim
  have hvm_shim : VmPreserved s_pre_shim sf_shim := by rwa [hs_pre, hsf_shim]
  rw [hs_pre, hsf_shim] at hvm_shim
  rw [← A.pool_of_vmPreserved hvm_shim]
  wp_steps
  wp_call halloc' (72, 8, st)
  apply with_wp_state; intro sf_alloc hsf_alloc
  have hx0_ne : sf_alloc.readReg64 Reg.x0 ≠ 0#64 := by rwa [hsf_alloc]
  rw [hsf_alloc] at hx0_ne
  have hoom_false : (_ == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
  simp only [memRegion_40_cells (k + 8#64),
    memRegion_72_cells,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro k0
  apply SepWP.exists_elim; intro k1
  apply SepWP.exists_elim; intro k2
  apply SepWP.exists_elim; intro k3
  apply SepWP.exists_elim; intro k4
  apply SepWP.exists_elim; intro u0
  apply SepWP.exists_elim; intro u1
  apply SepWP.exists_elim; intro u2
  apply SepWP.exists_elim; intro u3
  apply SepWP.exists_elim; intro u4
  apply SepWP.exists_elim; intro u5
  apply SepWP.exists_elim; intro u6
  apply SepWP.exists_elim; intro u7
  apply SepWP.exists_elim; intro u8
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_sync_pool (s0.readReg64 .lr)
  simp only [State.setMem_setMem]
  apply SepWP.fold (decodeErrorWith_zero_entails A.repAlloc _ w _ _ _ _ _ hkw)
    (by dsimp only [RustCliAllocBudget.repAlloc]; sep_focus)
  apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_focus)
  have henv : DecodeErrorFromEnv (rustAllocEvents 72 8) := rfl
  wp_done

theorem decode_error_from_placed_ok_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {hookStack : Nat}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim hookStack) :=
  decodeErrorFromWithStack_of_decodeErrorFrom
    (decode_error_from_placed_ok hshim halloc) hle hmax

theorem decode_error_from_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX) :=
  decode_error_from_placed_ok_gen hshim halloc

/-! ## Relocatable `prost::encoding::varint::decode_varint_slice` (block 76) -/

set_option maxHeartbeats 8000000 in
theorem decode_varint_slice_placed_ok_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {errStack : Nat}
    (herr : 0x50 + errStack ≤ 2 ^ 64 := by decide)
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim errStack)) :
    subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecGen A lim errStack)) := by
  have hFromCall := ls_subroutine_ok_cl_of_plain
    (callerProg := (blkPC_76).rebase (blkPl_76).base H) hFrom
  change subroutine_ok _ (lsmpl.base 261) _ at hFromCall
  clear hFrom
  unfold withLsCodeLoaded
  conv =>
    arg 3
    unfold decodeVarintSliceSpecGen
    simp only [memRegion_24_cells, stackAt_decodeVarintSliceGen herr, sepExists_sepConj_left,
      sepExists_sepConj_right]
  wpp_init x s0
  rcases x with ⟨⟨ret, ptr, bs⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have h : VarintSlicePre bs := by assumption
  have h_4 : bs.length < 2 ^ 63 := by assumption
  have hfits : FitsEnv M lim st (DecodeVarintSliceEnv bs) := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply eq_ofNat_of_toNat_eq; assumption
  obtain ⟨b0, bs1, rfl⟩ := exists_cons_of_all_gt (pre := []) h (by simp) (by rintro _ ⟨⟩)
  apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (16)) hcl0
  wp_steps_sync_pool ((blkPl_76).base + bv% (16))
  simp only [State.setMem_setMem]
  conv =>
    arg 4
    rw [pool_to_setMem A lim st s0
      ((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (16)))
      _ ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩]
  wp_reach
  intro hcl1
  suffices hjoin :
      ∀ m : Memory,
      LibsignalCodeLoaded lsmpl m →
      SepWPp ((blkPC_76).rebase (blkPl_76).base H) (s0.readReg64 Reg.lr)
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36)) |>.setMem m)
      (A.pool lim st (s0.setMem m) ∗
        ret ↦₆₄ v_stk_6 ∗ (ret + 8#64) ↦₆₄ v_stk_5 ∗ (ret + 16#64) ↦₆₄ v_stk_4 ∗
        (ptr ↦₈ b0 ∗ (ptr + 1#64) ↦ₛ bs1) ∗
        stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
        memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ v_stk_3 ∗
        (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗ (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
        (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨
              (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3, ∃∗ evs : List AllocEvent,
                ⌜sf.trace = s0.trace⌝ ∗
                  varintSliceResultAt A.repAlloc ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                  ptr ↦ₛ (b0 :: bs1) ∗
                  (⌜DecodeVarintSliceEnv (b0 :: bs1) evs⌝ ∗
                    A.pool lim (M.stepEvents evs st) sf) ∗
                  stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
                  memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                  (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ⌜False⌝ ∗ R) by
    by_cases h11 : 11 ≤ (b0 :: bs1).length
    · have hule11 := ule_11_of_ge h11 h_4
      apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl1
      conv => arg 4; rw [pointsToBytes_cons]
      wp_steps
      wp_reach
      intro hcl_j
      dsimp only [State.setMem] at hcl_j
      exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (hjoin _ hcl_j)
    · rcases h with h11' | ⟨hne, hlast⟩
      · exact (h11 h11').elim
      · have hule11 := ule_11_of_lt h11 h_4
        have hbit_last := getLsbD_7_beq_of_le hlast
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (32)) hcl1
        conv => arg 4; rw [pointsToBytes_split_last ptr (b0 :: bs1) hne h_4]
        wp_steps
        conv => arg 4; rw [← pointsToBytes_split_last ptr (b0 :: bs1) hne h_4, pointsToBytes_cons]
        wp_reach
        intro hcl2
        apply SepWPp.of_sepWP_lscl (mid := (blkPl_76).base + bv% (36)) hcl2
        wp_steps
        wp_reach
        intro hcl_j
        dsimp only [State.setMem] at hcl_j
        exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (hjoin _ hcl_j)
  intro m hcl_join
  by_cases hnone : decodeVarint (b0 :: bs1) = none
  · obtain ⟨b0', b1, b2, b3, b4, b5, b6, b7, b8, b9, rest, heq,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9⟩ := decodeVarint_eq_none_of_pre h hnone
    rcases heq with ⟨rfl, rfl⟩
    simp only [hnone, varintSliceResultAt]
    have hfits_de : FitsEnv M lim st DecodeErrorFromEnv := by
      refine hfits.mono fun evs he => ?_
      simpa only [DecodeVarintSliceEnv, decodeVarintSliceEvents, hnone, DecodeErrorFromEnv] using he
    have hbit0 := signExtend64_getLsbD_63_beq_of_gt hb0
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
    have hb9_ule := byte9_ule_of_ge hb9
    apply SepWPp.of_sepWP_lscl (mid := lsmpl.base 261) hcl_join
    conv =>
      arg 4
      simp only [pointsToBytes_cons]
      rw [← A.pool_of_vmPreserved (s0 := s0.setMem m)
        (sf := (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
            (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
          (subsPState64 (BitVec.ofNat 64 (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest).length) 11#64)).setPC ((blkPl_76).base + bv% (36)) |>.setMem m))
        ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩]
    wp_steps_sync_pool (lsmpl.base 261)
    simp only [State.setMem_setMem]
    wp_reach
    intro hcl_call
    refine SepWPp.call_frame_lscl
      (spec := decodeErrorFromBudgetSpecWithStack M A lim errStack)
      (x := (s0.sp - 64#64, 0x8000000000000001#64, st))
      (φ := KindNoHeap 0x8000000000000001#64 ∧ FitsEnv M lim st DecodeErrorFromEnv)
      (ret_pc := (blkPl_76).base + bv% (592)) hFromCall hcl_call
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [decodeErrorFromBudgetSpecWithStack, arm64_norm, true_and]; rfl)
      ⟨by decide, hfits_de⟩
      (by sep_focus)
      (fun _ _ _ _ hex => by
        simp only [decodeErrorFromBudgetSpecWithStack] at hex
        exact not_satisfies_false_sepConj hex)
      (fun _ _ hpan => by
        simp only [decodeErrorFromBudgetSpecWithStack, sepConj_assoc] at hpan
        exact False.elim (not_satisfies_false_sepConj hpan))
      ?_
      (fun _ _ _ hoom => by
        simp only [decodeErrorFromBudgetSpecWithStack] at hoom
        exact not_satisfies_false_sepConj hoom)
    intro sm hpcm hrunm hspm hcsm _
    simp only [CalleeSavedPreserved, arm64_norm] at hcsm
    apply SepWPp.of_sepWP_ret
    conv =>
      arg 4
      simp only [decodeErrorFromBudgetSpecWithStack, memRegion_48_split,
        sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
    apply SepWP.exists_elim; intro evs
    apply SepWP.exists_elim; intro v_err
    wp_steps_sync_pool (s0.readReg64 Reg.lr)
    simp only [State.setMem_setMem]
    apply SepWP.fold (pointsTo64_entails_memRegion8 (ret + 16#64) _) (by sep_focus)
    apply SepWP.done
    · simp only [arm64_norm]
    · simp only [arm64_norm, hrunm]
    · rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
      refine ⟨?_, by simp only [arm64_norm], ?_⟩
      · intro hm_final
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_final ⊢
        rcases hm_final with ⟨⟨⟨hx0_ne, htr⟩, hevs_de⟩, hm_final⟩
        have hevs_vs : DecodeVarintSliceEnv
            (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) evs := by
          simpa only [DecodeVarintSliceEnv, decodeVarintSliceEvents, hnone, DecodeErrorFromEnv]
            using hevs_de
        refine ⟨s0.readReg64 (Reg.gpr 30#5), s0.readReg64 (Reg.gpr 29#5), v_err, ret,
          evs, sm.readReg64 (Reg.gpr 0#5), ⟨htr, hx0_ne, hevs_vs⟩, ?_⟩
        arm64_sep_close
      · simp only [CalleeSavedPreserved, arm64_norm, hx19, hx20, hx21, hx22, hx23, hx24,
          hx25, hx26, hx27, hx28, hvregs]
  · apply SepWPp.of_sepWP_ret
    have hevs_ok : DecodeVarintSliceEnv (b0 :: bs1) [] := by
      simp only [DecodeVarintSliceEnv, decodeVarintSliceEvents]
      cases hd : decodeVarint (b0 :: bs1)
      · exact (hnone hd).elim
      · rfl
    let sJoin : State :=
      (((((s0.writeReg64 Reg.sp (s0.sp - 80#64)).writeReg64 (Reg.gpr 29#5) (s0.sp - 16#64)).writeReg64
          (Reg.gpr 8#5) (BitVec.signExtend 64 b0)).setPState
        (subsPState64 (BitVec.ofNat 64 (b0 :: bs1).length) 11#64)).setPC ((blkPl_76).base + bv% (36)) |>.setMem m)
    refine (?_ : SepWP _ _ sJoin _ (fun sf P_f => VmPreserved sJoin sf ∧
      ((sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (∃∗ x, ∃∗ x_1, ∃∗ x_2, ∃∗ x_3,
              ⌜sf.trace = s0.trace⌝ ∗
                varintSliceResultAt A.repAlloc ret (b0 :: bs1) (decodeVarint (b0 :: bs1)) ∗
                ptr ↦ₛ (b0 :: bs1) ∗
                A.pool lim st (s0.setMem m) ∗
                stackAt (s0.sp - 80#64) errStack ∗ memRegion (s0.sp - 80#64) 8 ∗
                memRegion (s0.sp - 56#64) 40 ∗ (s0.sp - 72#64) ↦₆₄ x_3 ∗
                (s0.sp - 64#64) ↦₆₄ x_2 ∗ (s0.sp - 16#64) ↦₆₄ x_1 ∗ (s0.sp - 8#64) ↦₆₄ x) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))).mono ?_
    swap
    · rintro sf P_f _ _ ⟨hvm, hmem_f, hsp_f, hcs_f⟩
      refine ⟨fun hm_f => ?_, hsp_f, hcs_f⟩
      have hvm0 : VmPreserved (s0.setMem m) sf :=
        VmPreserved.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩ hvm
      have hpool_eq : A.pool lim st (s0.setMem m) = A.pool lim (M.stepEvents [] st) sf := by
        change A.pool lim st (s0.setMem m) = A.pool lim st sf
        exact (A.pool_of_vmPreserved hvm0).symm
      have hm_f' := hmem_f hm_f
      clear hm_f hmem_f
      simp only [hpool_eq, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm] at hm_f' ⊢
      rcases hm_f' with ⟨y0, y1, y2, y3, htr, hm_f'⟩
      refine ⟨y0, y1, y2, y3, [], ⟨htr, hevs_ok⟩, ?_⟩
      exact hm_f'
    dsimp only [sJoin]
    by_vm_steps (
      by_cases hb0 : b0 ≤ 0x7f#8
      · have hbit0 := signExtend64_getLsbD_63_beq_of_le hb0
        rw [varintSliceResultAt_1 A.repAlloc ret b0 bs1 hb0]
        wp_steps
        wp_ret8_bv_bits ret (vAcc1 b0)
        conv => arg 4; simp only [← pointsToBytes_cons]
        wp_done
      · have hbit0 := signExtend64_getLsbD_63_beq_of_gt hb0
        obtain ⟨b1, bs2, rfl⟩ := exists_cons_of_all_gt (pre := [b0]) h (by simp)
          (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, hb0, not_false_eq_true])
        conv => arg 4; rw [pointsToBytes_cons]
        wp_steps 7
        by_cases hb1 : b1 ≤ 0x7f#8
        · have hbit1 := getLsbD_7_beq_of_le hb1
          rw [varintSliceResultAt_2 A.repAlloc ret b0 b1 bs2 hb0 hb1]
          wp_steps
          wp_ret8_bv_bits ret (vAcc2 b0 b1)
          conv => arg 4; simp only [← pointsToBytes_cons]
          wp_done
        · have hbit1 := getLsbD_7_beq_of_gt hb1
          have hovf2 := ovf_byte2 hb0 hb1
          obtain ⟨b2, bs3, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1]) h (by simp)
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              hb0, hb1, not_false_eq_true, and_self])
          conv => arg 4; rw [pointsToBytes_cons]
          wp_steps 7
          by_cases hb2 : b2 ≤ 0x7f#8
          · have hbit2 := getLsbD_7_beq_of_le hb2
            rw [varintSliceResultAt_3 A.repAlloc ret b0 b1 b2 bs3 hb0 hb1 hb2]
            wp_steps
            wp_ret8_bv_bits ret (vAcc3 b0 b1 b2)
            conv => arg 4; simp only [← pointsToBytes_cons]
            wp_done
          · have hbit2 := getLsbD_7_beq_of_gt hb2
            have hovf3 := ovf_byte3 hb0 hb1 hb2
            obtain ⟨b3, bs4, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2]) h (by simp)
              (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                hb0, hb1, hb2, not_false_eq_true, and_self])
            conv => arg 4; rw [pointsToBytes_cons]
            wp_steps 7
            by_cases hb3 : b3 ≤ 0x7f#8
            · have hbit3 := getLsbD_7_beq_of_le hb3
              rw [varintSliceResultAt_4 A.repAlloc ret b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3]
              wp_steps
              wp_ret8_bv_bits ret (vAcc4 b0 b1 b2 b3)
              conv => arg 4; simp only [← pointsToBytes_cons]
              wp_done
            · have hbit3 := getLsbD_7_beq_of_gt hb3
              have hovf4 := ovf_byte4_zext hb0 hb1 hb2 hb3
              obtain ⟨b4, bs5, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3]) h (by simp)
                (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                  hb0, hb1, hb2, hb3, not_false_eq_true, and_self])
              conv => arg 4; rw [pointsToBytes_cons]
              wp_steps 7
              by_cases hb4 : b4 ≤ 0x7f#8
              · have hbit4 := getLsbD_7_beq_of_le hb4
                rw [varintSliceResultAt_5 A.repAlloc ret b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4]
                wp_steps
                wp_ret8_bv_bits ret (vAcc5 b0 b1 b2 b3 b4)
                conv => arg 4; simp only [← pointsToBytes_cons]
                wp_done
              · have hbit4 := getLsbD_7_beq_of_gt hb4
                obtain ⟨b5, bs6, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4]) h (by simp)
                  (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
                    hb0, hb1, hb2, hb3, hb4, not_false_eq_true, and_self])
                conv => arg 4; rw [pointsToBytes_cons]
                wp_steps 5
                by_cases hb5 : b5 ≤ 0x7f#8
                · have hbit5 := getLsbD_7_beq_of_le hb5
                  rw [varintSliceResultAt_6 A.repAlloc ret b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5]
                  wp_steps
                  wp_ret8_bv_bits ret (vAcc6 b0 b1 b2 b3 b4 b5)
                  conv => arg 4; simp only [← pointsToBytes_cons]
                  wp_done
                · have hbit5 := getLsbD_7_beq_of_gt hb5
                  have hovf6 := ovf_byte6 hb4 hb5
                  obtain ⟨b6, bs7, rfl⟩ := exists_cons_of_all_gt (pre := [b0, b1, b2, b3, b4, b5]) h
                    (by simp) (by simp only [List.mem_cons, List.not_mem_nil, or_false,
                      forall_eq_or_imp, forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, not_false_eq_true,
                      and_self])
                  conv => arg 4; rw [pointsToBytes_cons]
                  wp_steps 7
                  by_cases hb6 : b6 ≤ 0x7f#8
                  · have hbit6 := getLsbD_7_beq_of_le hb6
                    rw [varintSliceResultAt_7 A.repAlloc ret b0 b1 b2 b3 b4 b5 b6 bs7
                      hb0 hb1 hb2 hb3 hb4 hb5 hb6]
                    wp_steps
                    wp_ret8_bv_bits ret (vAcc7 b0 b1 b2 b3 b4 b5 b6)
                    conv => arg 4; simp only [← pointsToBytes_cons]
                    wp_done
                  · have hbit6 := getLsbD_7_beq_of_gt hb6
                    have hovf7 := ovf_byte7 hb4 hb5 hb6
                    obtain ⟨b7, bs8, rfl⟩ := exists_cons_of_all_gt
                      (pre := [b0, b1, b2, b3, b4, b5, b6]) h (by simp)
                      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                        forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, not_false_eq_true, and_self])
                    conv => arg 4; rw [pointsToBytes_cons]
                    wp_steps 7
                    by_cases hb7 : b7 ≤ 0x7f#8
                    · have hbit7 := getLsbD_7_beq_of_le hb7
                      rw [varintSliceResultAt_8 A.repAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 bs8
                        hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7]
                      wp_steps
                      wp_ret8_bv_bits ret (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7)
                      conv => arg 4; simp only [← pointsToBytes_cons]
                      wp_done
                    · have hbit7 := getLsbD_7_beq_of_gt hb7
                      have hovf8 := ovf_byte8_zext hb4 hb5 hb6 hb7
                      obtain ⟨b8, bs9, rfl⟩ := exists_cons_of_all_gt
                        (pre := [b0, b1, b2, b3, b4, b5, b6, b7]) h (by simp)
                        (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
                          forall_eq, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, not_false_eq_true,
                          and_self])
                      conv => arg 4; rw [pointsToBytes_cons]
                      wp_steps 7
                      by_cases hb8 : b8 ≤ 0x7f#8
                      · have hbit8 := signExtend64_getLsbD_63_beq_of_le hb8
                        rw [varintSliceResultAt_9 A.repAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9
                          hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8]
                        wp_steps
                        wp_ret8_bv_bits ret (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8)
                        conv => arg 4; simp only [← pointsToBytes_cons]
                        wp_done
                      · have hbit8 := signExtend64_getLsbD_63_beq_of_gt hb8
                        obtain ⟨b9, bs10, rfl⟩ := exists_cons_of_all_gt
                          (pre := [b0, b1, b2, b3, b4, b5, b6, b7, b8]) h (by simp)
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
                        have hb9_ule := byte9_ule_of_lt hb9
                        have hovf10 := ovf_byte10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
                        conv => arg 4; rw [pointsToBytes_cons]
                        rw [varintSliceResultAt_10 A.repAlloc ret b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10
                          hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9]
                        wp_steps
                        wp_ret8_bv_bits ret (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)
                        conv => arg 4; simp only [← pointsToBytes_cons]
                        wp_done)

theorem decode_varint_slice_placed_ok_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpec M A lim)) :
    DecodeVarintSlicePlacedOk A lim H :=
  decode_varint_slice_placed_ok_gen (errStack := decodeErrorHookStack) (by decide)
    (decodeErrorFromWithStack_of_decodeErrorFrom hFrom)

theorem decode_varint_slice_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    DecodeVarintSlicePlacedOk A lim H :=
  decode_varint_slice_placed_ok_of_contract
    (decode_error_from_placed_ok hshim halloc)

theorem decode_varint_slice_placed_ok_of_contract_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)) :
    DecodeVarintSlicePlacedOkX A lim H :=
  decode_varint_slice_placed_ok_gen (errStack := decodeErrorHookStackX) (by decide) hFrom

theorem decode_varint_slice_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    DecodeVarintSlicePlacedOkX A lim H :=
  decode_varint_slice_placed_ok_of_contract_x
    (decode_error_from_placed_ok_x hshim halloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
