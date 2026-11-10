/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Base Step Lemmas for `encode_varint::<Vec<u8>> [local#4]` (Block `451`)

Threads `RustCliAllocBudget` and `VmPreserved` through prologue capacity checks and
continuation-byte stages 1–3 and 9 for Block `451`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed
  (blkPC_460 blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed
  (blkPC_451 blkPl_451 lsProg_451)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncodeVarintGhost vecU8Buf vecU8At_eq_header_sep_buf vecU8Buf_eq_open_one vecU8Buf_snoc_eq
   cap_beq_len_false cap_eq_ofNat_len bv_len_add_one sepWPp_extract_vecU8Buf_le
   varintContByte EncVarintCalleeSavedPlaced stackAt_encodeVarint_gen_eq
   contByte9_contByte_eq)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents encodeVarintEvents encodeVarintEnv_events)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (pushByteStep_of_lt VecPushBudgetInv sepWPp_of_sepWP_cs_placed_vm sepWPp_of_sepWP_vm
   encodeVarintSpecOf final_frame_reassoc stage_frame_reassoc)
open LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.DoReservePlacedBudget
  (do_reserve_2_raw1_placed_ok do_reserve_2_raw1_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2BaseBudget
  (do_reserve2_placed_of_raw1)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
  (encodeVarintFitSpec encodeVarintFitSpecX)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserveSpecOf doReserve2SpecOf doReserve2Spec doReserve2SpecX doReserve2SpecWithPlaced
   step_doReserve2_call_gen_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev EncodeVarint2FitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_451 H) (blkPl_451).base
    (withLsCodeLoaded lsmpl (encodeVarintFitSpec A lim))

abbrev EncodeVarint2FitPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_451 H) (blkPl_451).base
    (withLsCodeLoaded lsmpl (encodeVarintFitSpecX A lim))

theorem do_reserve2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve2Spec A lim)) :=
  do_reserve2_placed_of_raw1 (hookStack := allocHookStack)
    (do_reserve_2_raw1_placed_ok h_panic hshim halloc hrealloc)

theorem do_reserve2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_460).rebase (blkPl_460).base H) (blkPl_460).base
      (withLsCodeLoaded lsmpl (doReserve2SpecX A lim)) :=
  do_reserve2_placed_of_raw1 (hookStack := extHookStack)
    (do_reserve_2_raw1_placed_ok_x h_panic hshim halloc hrealloc)

/-- `doReserve2Spec A lim` entails `doReserve2SpecX A lim` by framing the unused bottom stack region. -/

abbrev doReserve2_placed_ok := @do_reserve2_placed_ok
abbrev doReserve2_placed_ok_x := @do_reserve2_placed_ok_x

/-! ## 1. Placed Step Lemmas for `encode_varint [local#4]` (Block `451`, calling Block `460`) -/

theorem step_encVarint2_prologue_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8)) (st0 : M.σ)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗ A.pool lim st0 s) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 32#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s.trace →
      sm.readReg64 .x0 = val → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length → sm.readReg64 .x9 = cap →
      EncVarintCalleeSavedPlaced s sm →
      SepWPp (lsProg_451 H) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19) ∗
          A.pool lim st0 sm) ∗ F) Q Qp) :
    SepWPp (lsProg_451 H) ret s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_cs_placed_vm
    (mid := if val.ult 128#64 then (blkPl_451).base + bv% (868) else (blkPl_451).base + bv% (32))
  by_vm_steps
    wp_steps
    refine SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
    rw [← A.pool_of_vmPreserved hvm]
    exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self])

theorem step_encVarint2_final_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗ ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sf : State) (cap' ptr' : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → curCap.toNat ≤ cap'.toNat →
      (curBs.length < curCap.toNat → cap' = curCap ∧ ptr' = curPtr) →
      cap'.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      Q sf (((v ↦₆₄ cap') ∗ ((v + 8#64) ↦₆₄ ptr') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A.repAlloc cap' ptr' (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sf ∗
        stackAt (sp - 48#64) resStack) ∗ F)) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
    have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm => ?_⟩
      apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt,
        ← A.pool_of_vmPreserved hvm, ← hst_eq]
      exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by encodedLen_cc_close) (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 460)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve2_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_451).base + bv% (932)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗ ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      rcases hcsm with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs, _⟩
      have hx19m' : sm.readReg64 .x19 = lastVal := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = v := by simp only [arm64_norm, *]
      have hbeq := cap_beq_len_false hnew_gt; have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm2 => ?_⟩
        apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (BitVec.zeroExtend 8 lastVal) hnew_gt,
          ← A.pool_of_vmPreserved hvm2, final_frame_reassoc]
        exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by encodedLen_cc_close) hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint2_exit_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintSpecOf resStack A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  refine step_encVarint2_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hres' := hinv'.res; rw [hbs] at hres'; have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa [pushBytesEvents] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩; intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]
  convert hm_f using 1; sep_ac_rfl

/-! ## 2. Placed Continuation-Byte Stages 1..3 and 9 (Block `451`) -/

theorem step_encVarint2_s1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 7).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte val]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 7).ult 128#64 = true ∨ (val >>> 7).ult 128#64 = false := by
    cases (val >>> 7).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte val)
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (128))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte val) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 460)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve2_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_451).base + bv% (96)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hlen1 := bv_len_add_one curBs (varintContByte val)
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (128))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte val) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint2_s2_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 14).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 236#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x10 = nextPtr → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 7)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 14).ult 128#64 = true ∨ (val >>> 14).ult 128#64 = false := by
    cases (val >>> 14).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (236))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 7)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 460)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve2_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_451).base + bv% (200)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 7)) |||
            4294967168#64 := by
        simp only [arm64_norm, *]; simp
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v48 val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (236))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 7)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v48 val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint2_s3_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 236#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr) (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr v48' v40' : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then (blkPl_451).base + 868#64 else (blkPl_451).base + 336#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v → sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = nextCap → sm.readReg64 .x12 = val >>> 28 → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          ((sp - 48#64) ↦₆₄ v48') ∗ ((sp - 40#64) ↦₆₄ v40') ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt; have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (336))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr v48 v40
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 460)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve2_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_451).base + bv% (304)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq)
        (F := ((sp - 48#64) ↦₆₄ v) ∗ ((sp - 40#64) ↦₆₄ val) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 =
          BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 val) >>> 14)) |||
            4294967168#64 := by
        simp only [arm64_norm, *]; simp
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (336))
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step' => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, stage_frame_reassoc]
          exact hnext _ newCap p' v val
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) hcap_step

theorem step_encVarint2_s9_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (val v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hnot_ult : (val >>> 56).ult 128#64 = false)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_res : curCap.toNat = curBs.length →
      FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = val >>> 56) (hx11 : s.readReg64 .x11 = curPtr)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_451).base + 868#64 → sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = 1#64 → sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length →
      sm.readReg64 .x9 = nextCap → EncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat → (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1 →
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 56)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 56)]) ∗
          A.pool lim (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) sm ∗
          stackAt (sp - 48#64) resStack) ∗ F) Q Qp) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 48#64) resStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hbyte := contByte9_contByte_eq val hnot_ult
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
    have hstep_lt := pushByteStep_of_lt hlt
    have hst_eq : M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 56)) hlt,
        ← A.pool_of_vmPreserved hvm, ← hst_eq]
      exact hnext _ curCap curPtr
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 460)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_doReserve2_call_gen_placed A lim hdoReserve v curCap curPtr sp
        ((blkPl_451).base + bv% (972)) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_res hcap_eq) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hcsm hnew_gt hnew_ge hcap_step
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val >>> 56 := by simp only [arm64_norm, *]
      have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 56))
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_451).base + bv% (868))
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 56)) hnew_gt,
          ← A.pool_of_vmPreserved hvm2]
        exact hnext _ newCap p'
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcsm.trans (by simp only [EncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          hnew_ge (fun h => absurd h hlt) hcap_step

end LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
