/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Handshake `finish_grow [local#9]` and `do_reserve_and_handle [local#8]`

Verifies `[LibsignalPlacement]` `<RawVecInner>::finish_grow [local#9]` (Block `522`) and
`<RawVecInner>::reserve::do_reserve_and_handle [local#8]` (Block `517`) under `RustCliAllocBudget`
and `VmPreserved`, lifting their contracts to `lsProg_518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10PlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lscall_blk lsHandleErrorSym lsRustAllocSym
  lsRustNoAllocShimSym lsRustReallocSym lsmpl lsρ sepWP_seq_lscl
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (
  SepWP.instantiate_post_exists extHookStack ls_externAt?_of_caller reserveCap
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (
  FinishGrow1Call adds_cs_eq_false finishGrow32Stack memRegion_24 reserve_new_cap_eq
  stackAt_doReserve32
)
open CryptoVerification.CliHandshake.Placed (
  blkPl_517 blkPl_522 lsProg_517 lsProg_522
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget (
  FinishGrow1Env doReserve1Raw32Spec doReserve1RawSpec doReserve1VecSpecX
  do_reserve_raw1_of_raw32_lscl do_reserve_raw_of_raw1_lscl
  do_reserve_vec1_of_raw1_lscl do_reserve_vec_of_raw_lscl
  finishGrow1AllocSpec finishGrow1Events finishGrow1ReallocSpec finishGrow1Spec
  finish_grow_11_of_zero_ne finish_grow_24_ne_cells_of_spec finish_grow_24_zero_cells_of_spec
  fitsEnv_finishGrow1_iff
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget (
  session2ShimSpecWithStack session2ShimWithStack_of_noAllocShim
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  DoReserveEnv doReserveEvents doReserveRawSpecX doReserveSpecX fitsEnv_doReserve_iff
  noAllocShimSpec
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.ReserveNorm (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`<alloc::raw_vec::RawVecInner>::finish_grow [local#9]`
(Block `522`, `(blkPl_522).base = lsmpl.base 522`) on `lsProg_518 ext`. -/
def FinishGrow11PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 522)
    (withLsCl lsmpl (finishGrow1Spec M A lim))

/-- Relocatable `[LibsignalPlacement]` raw 1-byte budget-threaded `do_reserve_and_handle [local#8]`
contract (Block `517`, `(blkPl_517).base = lsmpl.base 517`) on `lsProg_518 ext`. -/
def DoReserve10PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 517)
    (withLsCl lsmpl (doReserveSpecX M A lim))

/-- Relocatable `[LibsignalPlacement]` `Vec<u8>` budget-threaded `do_reserve_and_handle [local#8]`
contract (Block `517`, `(blkPl_517).base = lsmpl.base 517`) on `lsProg_518 ext`. -/
def DoReserve10VecPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 517)
    (withLsCl lsmpl (doReserve1VecSpecX M A lim))

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem stackAt_finishGrow32 (sp : BitVec 64) :
    stackAt sp finishGrow32Stack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp 16384 4 (by decide)

theorem finish_grow_11_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_522 H)
      (lsρ lsRustNoAllocShimSym) (session2ShimSpecWithStack extHookStack))
    (halloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1AllocSpec M A lim) := by
  unfold finishGrow1AllocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
      BitVec.toNat_zero, Nat.mul_one, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
    BitVec.toNat_zero, Nat.mul_one, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_11_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hrealloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1ReallocSpec M A lim) := by
  unfold finishGrow1ReallocSpec finishGrow1Spec
  simp only [memRegion_24, stackAt_finishGrow32,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hcap_toNat_ne : cap.toNat ≠ 0 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
      hcap_toNat_ne, Nat.mul_one, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, hpow, by omega⟩, by decide⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ lsRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
    hcap_toNat_ne, Nat.mul_one, ↓reduceIte]
  wp_done

theorem finish_grow_11_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_522 H)
      (lsρ lsRustNoAllocShimSym) (session2ShimSpecWithStack extHookStack))
    (halloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false extHookStack))
    (hrealloc : subroutine_ok (lsProg_522 H)
      (lsρ lsRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim extHookStack)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1Spec M A lim) :=
  finish_grow_11_of_zero_ne
    (finish_grow_11_zero_placed_ok_of_hooks hshim halloc)
    (finish_grow_11_ne_placed_ok_of_hooks hrealloc)

theorem do_reserve_10_raw32_placed_ok_of_fg [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (_h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hfg : subroutine_ok (lsProg_522 H) (blkPl_522).base (finishGrow1Spec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)) := by
  unfold withLsCodeLoaded doReserve1Raw32Spec
  simp only [stackAt_doReserve32, sepExists_sepConj_right]
  wp_init x s0
  rcases x with ⟨⟨v, cap, ptr, bs, additional⟩, st⟩
  dsimp only at *
  have hcl : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx1_eq : (s0.readReg64 .x1).toNat = bs.length := by assumption
  have hx2_eq : (s0.readReg64 .x2).toNat = additional := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hbound : reserveCap cap.toNat bs.length additional + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (DoReserveEnv ⟨v, cap, ptr, bs, additional⟩) := by assumption
  have hcs := adds_cs_eq_false (x2 := s0.readReg64 .x2) (x1 := s0.readReg64 .x1) (by
    dsimp [reserveCap] at hbound; rw [hx2_eq, hx1_eq]; omega)
  have hnew_eq := reserve_new_cap_eq (cap := cap) hx1_eq hx2_eq hbound
  let new := BitVec.ofNat 64 (reserveCap cap.toNat bs.length additional)
  have hnew_toNat : new.toNat = reserveCap cap.toNat bs.length additional := by
    dsimp [new, reserveCap] at hbound ⊢; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_le_new : cap.toNat ≤ new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_pos : 0 < new.toNat := by dsimp [reserveCap] at hnew_toNat; omega
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbs_le_cap)
    subst hbs
    have hfits : FitsEvents M lim st (finishGrow1Events 0 new.toNat) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, finishGrow1Events,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
        Nat.mul_one, ↓reduceIte, hnew_toNat] using hfits_env
    have hnew_eq0 :
        (if (8#64).ult
              (if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
                s0.readReg64 .x2 + s0.readReg64 .x1
               else 0#64) = true then
          if (0#64).ult (s0.readReg64 .x2 + s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x1
          else 0#64
         else 8#64) = new := hnew_eq
    simp only [emp_sepConj, pointsToBytes_nil,
      List.length_nil, BitVec.add_zero, Nat.sub_zero, doReserveEvents, ↓reduceIte]
    rw [show rustAllocEvents (reserveCap (0#64 : BitVec 64).toNat 0 additional) 1 =
      finishGrow1Events 0 new.toNat by
      simp only [finishGrow1Events,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
        List.length_nil, Nat.mul_one, ↓reduceIte, hnew_toNat]]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 522)
    wp_steps_sync_pool (lsmpl.base 522)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg0 := lscall_blk (callerProg := lsProg_517 H)
      (finish_grow_24_zero_cells_of_spec hfg) hcl_m
    wp_call hfg0 ((s0.sp - 56#64, 0#64, ptr, new, [], v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    dsimp only [new]
    wp_done
  · have hcap_pos : 0 < cap.toNat :=
      Nat.pos_of_ne_zero (fun hc => hcap0 (BitVec.eq_of_toNat_eq hc))
    have hcap_toNat_ne : cap.toNat ≠ 0 := by omega
    have hfits : FitsEvents M lim st (finishGrow1Events cap.toNat new.toNat) := by
      rw [fitsEnv_doReserve_iff] at hfits_env
      simpa only [doReserveEvents, finishGrow1Events,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
        hcap0, hcap_toNat_ne, Nat.mul_one, ↓reduceIte, hnew_toNat] using hfits_env
    simp only [hcap0, doReserveEvents, ↓reduceIte, sepConj_assoc]
    rw [show rustReallocEvents cap.toNat (reserveCap cap.toNat bs.length additional) 1 =
      finishGrow1Events cap.toNat new.toNat by
      simp only [finishGrow1Events,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.finishGrowEvents,
        hcap_toNat_ne, Nat.mul_one, ↓reduceIte, hnew_toNat]]
    rw [show reserveCap cap.toNat bs.length additional - bs.length = new.toNat - bs.length by
      rw [hnew_toNat]]
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 522)
    wp_steps_sync_pool (lsmpl.base 522)
    simp only [State.setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
    intro hcl_m
    have hfg1 := lscall_blk (callerProg := lsProg_517 H)
      (finish_grow_24_ne_cells_of_spec hfg) hcl_m
    wp_call hfg1 ((s0.sp - 56#64, cap, ptr, new, bs, v_stk_1, v_stk_2, v_stk_3, s0.sp - 64#64), st)
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    simp only [State.setMem_setMem]
    dsimp only [new]
    wp_done

theorem finish_grow_11_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_522 H) (blkPl_522).base
      (finishGrow1Spec M A lim) :=
  finish_grow_11_placed_ok_of_hooks
    (session2ShimWithStack_of_noAllocShim extHookStack
      (ls_hook_ok_of_mem (prog := lsProg_522 H) (i := 522) hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc ls_externAt?_of_caller)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc ls_externAt?_of_caller)

theorem finish_grow_11_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    FinishGrow11PlacedOkExt A lim H :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_518 H)
    (finish_grow_11_placed_ok hshim halloc hrealloc)

theorem do_reserve_10_raw32_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1Raw32Spec M A lim)) :=
  do_reserve_10_raw32_placed_ok_of_fg h_panic
    (finish_grow_11_placed_ok hshim halloc hrealloc)

theorem do_reserve_10_raw1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1RawSpec M A lim)) :=
  do_reserve_raw1_of_raw32_lscl
    (do_reserve_10_raw32_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_raw_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserveRawSpecX M A lim)) :=
  do_reserve_raw_of_raw1_lscl
    (do_reserve_10_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserveSpecX M A lim)) :=
  do_reserve_vec_of_raw_lscl
    (do_reserve_10_raw_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_vec1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_517 H) (blkPl_517).base
      (withLsCodeLoaded lsmpl (doReserve1VecSpecX M A lim)) :=
  do_reserve_vec1_of_raw1_lscl
    (do_reserve_10_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    DoReserve10PlacedOkExtX A lim H :=
  ls_subroutine_ok_cl_of_block (callerProg := lsProg_518 H)
    (do_reserve_10_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve_10_vec_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H lsHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    DoReserve10VecPlacedOkExtX A lim H :=
  ls_subroutine_ok_cl_of_block (callerProg := lsProg_518 H)
    (do_reserve_10_vec1_placed_ok h_panic hshim halloc hrealloc)

abbrev doReserve10_placed_ok := @do_reserve_10_placed_ok_ext_x

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10PlacedBudget
