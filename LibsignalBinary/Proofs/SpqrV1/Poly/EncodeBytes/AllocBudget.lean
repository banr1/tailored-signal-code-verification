/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Alloc
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.LoopBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Heap Allocations and Header Init for `<PolyEncoder as Encoder>::encode_bytes`

Threads `RustCliAllocBudget M`, `encodeBytesAllocChunkEvents`, and `VmPreserved` through the four
4-allocation chunks (`+96..+476`) and stack-header initialization on Block `417`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.AllocBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkLib_eq_417 blkPC_417 blkPl_417 lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSessionRepr (VecPin)
open CryptoVerification.LibsignalSpqrV1 (Point)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem
)
open CryptoVerification.SpqrV1.Poly (pointListPinAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (bv_add_add_lit exists_pow_two_eq_two)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (
  subroutine_ok_allocNoOomWithStack_of_budget
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (
  blk417_safeVm encodeBytesAllocEvents isTotalTrapHooks_withPanics_vmTrapHooks
  sepWP_lsBlock_vmPreserved stripS_calleeSavedVRegs stripS_pc stripS_readReg64
  stripS_sp stripS_status stripS_trace vmTrapHooks
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustAllocNoOomSpecWithStack)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero exists_pow_two_eq_two bv_add_add_lit

private noncomputable abbrev keep417 [LibsignalPlacement] : BitVec 64 → Bool :=
  ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))

/-! ## 4-Allocation Chunk Event Schedule and `encodeBytesAllocEvents` Decomposition -/

/-- Exact allocator event list of one 4-allocation chunk (`4 × __rust_alloc(msgLen, 2)`). -/
def encodeBytesAllocChunkEvents (msgLen : Nat) : List AllocEvent :=
  rustAllocEvents msgLen 2 ++
    (rustAllocEvents msgLen 2 ++
      (rustAllocEvents msgLen 2 ++ rustAllocEvents msgLen 2))

theorem encodeBytesAllocChunkEvents_eq_replicate (msgLen : Nat) :
    encodeBytesAllocChunkEvents msgLen = (List.replicate 4 (rustAllocEvents msgLen 2)).flatten := by
  simp [encodeBytesAllocChunkEvents, List.replicate]

theorem encodeBytesAllocEvents_eq_chunks {msgLen : Nat}
    (hle : msgLen ≤ 1048576) (heven : msgLen % 2 = 0) (hpos : 0 < msgLen) :
    encodeBytesAllocEvents msgLen =
      encodeBytesAllocChunkEvents msgLen ++
        (encodeBytesAllocChunkEvents msgLen ++
          (encodeBytesAllocChunkEvents msgLen ++ encodeBytesAllocChunkEvents msgLen)) := by
  have hcond : msgLen ≤ 1048576 ∧ msgLen % 2 = 0 ∧ 0 < msgLen := ⟨hle, heven, hpos⟩
  simp only [encodeBytesAllocEvents, hcond, and_self, ↓reduceIte, encodeBytesAllocChunkEvents,
    List.replicate, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem fitsEvents_encodeBytesAllocChunk {M : AllocCostModel} {lim : BudgetLimits}
    {msgLen : Nat} {st0 : M.σ}
    (hfits : FitsEvents M lim st0 (encodeBytesAllocChunkEvents msgLen)) :
    let e := rustAllocEvents msgLen 2
    let st1 := M.stepEvents e st0
    let st2 := M.stepEvents e st1
    let st3 := M.stepEvents e st2
    FitsEvents M lim st0 e ∧
      FitsEvents M lim st1 e ∧
      FitsEvents M lim st2 e ∧
      FitsEvents M lim st3 e ∧
      M.stepEvents e st3 = M.stepEvents (encodeBytesAllocChunkEvents msgLen) st0 := by
  dsimp only [encodeBytesAllocChunkEvents] at hfits ⊢
  obtain ⟨hf0, hf123⟩ := (fitsEvents_append M lim _ _ _).mp hfits
  obtain ⟨hf1, hf23⟩ := (fitsEvents_append M lim _ _ _).mp hf123
  obtain ⟨hf2, hf3⟩ := (fitsEvents_append M lim _ _ _).mp hf23
  refine ⟨hf0, hf1, hf2, hf3, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]

theorem fitsEvents_encodeBytesAllocEvents_chunks {M : AllocCostModel} {lim : BudgetLimits}
    {msgLen : Nat} {st0 : M.σ}
    (hle : msgLen ≤ 1048576) (heven : msgLen % 2 = 0) (hpos : 0 < msgLen)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocEvents msgLen)) :
    let c := encodeBytesAllocChunkEvents msgLen
    let st1 := M.stepEvents c st0
    let st2 := M.stepEvents c st1
    let st3 := M.stepEvents c st2
    FitsEvents M lim st0 c ∧
      FitsEvents M lim st1 c ∧
      FitsEvents M lim st2 c ∧
      FitsEvents M lim st3 c ∧
      M.stepEvents c st3 = M.stepEvents (encodeBytesAllocEvents msgLen) st0 := by
  rw [encodeBytesAllocEvents_eq_chunks hle heven hpos] at hfits ⊢
  obtain ⟨hc0, hc123⟩ := (fitsEvents_append M lim _ _ _).mp hfits
  obtain ⟨hc1, hc23⟩ := (fitsEvents_append M lim _ _ _).mp hc123
  obtain ⟨hc2, hc3⟩ := (fitsEvents_append M lim _ _ _).mp hc23
  refine ⟨hc0, hc1, hc2, hc3, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]

/-! ## Relocatable `[LibsignalPlacement]` 4-Allocation Chunk Proofs (Block `417`) -/

section Placed
variable [LibsignalPlacement]

set_option maxHeartbeats 800000 in
theorem encode_bytes_alloc_0_3_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (s0 s : State) (st0 : M.σ) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocChunkEvents msgLen))
    (v5 v6 v7 v8 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 96#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p0 p1 p2 p3 : BitVec 64),
      p0 ≠ 0 → p1 ≠ 0 → p2 ≠ 0 → p3 ≠ 0 →
      s4.pc = (blkPl_417).base + 192#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool lim (M.stepEvents (encodeBytesAllocChunkEvents msgLen) st0) s4 ∗
          ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗
          ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
          (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗
          (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
          (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗
          (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st0 s ∗
        ((fsp + 40#64) ↦₆₄ v5) ∗ ((fsp + 48#64) ↦₆₄ v6) ∗
        ((fsp + 56#64) ↦₆₄ v7) ∗ ((fsp + 64#64) ↦₆₄ v8) ∗
        stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk msgLen 2 := ⟨⟨by omega, hpow2, by omega⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  obtain ⟨hf0, hf1, hf2, hf3, hstep_chunk⟩ := fitsEvents_encodeBytesAllocChunk hfits
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc_raw : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem halloc_sat
  have halloc := subroutine_ok_allocNoOomWithStack_of_budget (stk := allocHookStack) halloc_raw
  simp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  simp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat, Bool.false_eq_true, ↓reduceIte] at halloc
  let st1 := M.stepEvents (rustAllocEvents msgLen 2) st0
  let st2 := M.stepEvents (rustAllocEvents msgLen 2) st1
  let st3 := M.stepEvents (rustAllocEvents msgLen 2) st2
  have hsp_align : s.spAligned = true := by simpa [State.spAligned, hsp] using hfsp_align
  wp_norm_hyp hpc; wp_norm_hyp hsp_align; wp_norm_hyp hx21
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 192#64)
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st0)
  have htr0 := (‹Heap.AllocCallPreserved _ sf_1›).2.1
  have hoom0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st1)
  have htr1 := (‹Heap.AllocCallPreserved _ sf_3›).2.1
  have hoom1 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st2)
  have htr2 := (‹Heap.AllocCallPreserved _ sf_5›).2.1
  have hoom2 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st3)
  have htr3 := (‹Heap.AllocCallPreserved _ sf_7›).2.1
  have hoom3 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
  wp_steps_sync_pool ((blkPl_417).base + 192#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rw [hstep_chunk]
  refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
    hoom0 hoom1 hoom2 hoom3 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [arm64_norm, wp_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [arm64_norm, wp_norm, *]

set_option maxHeartbeats 800000 in
theorem encode_bytes_alloc_4_7_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (s0 s : State) (st0 : M.σ) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocChunkEvents msgLen))
    (v1 v2 v3 v4 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 192#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p4 p5 p6 p7 : BitVec 64),
      p4 ≠ 0 → p5 ≠ 0 → p6 ≠ 0 → p7 ≠ 0 →
      s4.pc = (blkPl_417).base + 288#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool lim (M.stepEvents (encodeBytesAllocChunkEvents msgLen) st0) s4 ∗
          ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗
          ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
          (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗
          (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
          (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗
          (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st0 s ∗
        ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
        ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗
        stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk msgLen 2 := ⟨⟨by omega, hpow2, by omega⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  obtain ⟨hf0, hf1, hf2, hf3, hstep_chunk⟩ := fitsEvents_encodeBytesAllocChunk hfits
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc_raw : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem halloc_sat
  have halloc := subroutine_ok_allocNoOomWithStack_of_budget (stk := allocHookStack) halloc_raw
  simp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  simp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat, Bool.false_eq_true, ↓reduceIte] at halloc
  let st1 := M.stepEvents (rustAllocEvents msgLen 2) st0
  let st2 := M.stepEvents (rustAllocEvents msgLen 2) st1
  let st3 := M.stepEvents (rustAllocEvents msgLen 2) st2
  have hsp_align : s.spAligned = true := by simpa [State.spAligned, hsp] using hfsp_align
  wp_norm_hyp hpc; wp_norm_hyp hsp_align; wp_norm_hyp hx21
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 288#64)
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st0)
  have htr4 := (‹Heap.AllocCallPreserved _ sf_1›).2.1
  have hoom4 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st1)
  have htr5 := (‹Heap.AllocCallPreserved _ sf_3›).2.1
  have hoom5 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st2)
  have htr6 := (‹Heap.AllocCallPreserved _ sf_5›).2.1
  have hoom6 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st3)
  have htr7 := (‹Heap.AllocCallPreserved _ sf_7›).2.1
  have hoom7 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
  wp_steps_sync_pool ((blkPl_417).base + 288#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rw [hstep_chunk]
  refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
    hoom4 hoom5 hoom6 hoom7 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [arm64_norm, wp_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [arm64_norm, wp_norm, *]

set_option maxHeartbeats 800000 in
theorem encode_bytes_alloc_8_11_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (s0 s : State) (st0 : M.σ) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocChunkEvents msgLen))
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 288#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0 → p9 ≠ 0 → p10 ≠ 0 → p11 ≠ 0 →
      s4.pc = (blkPl_417).base + 384#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = p8 → s4.readReg64 .x24 = p9 →
      s4.readReg64 .x25 = p10 → s4.readReg64 .x26 = p11 →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool lim (M.stepEvents (encodeBytesAllocChunkEvents msgLen) st0) s4 ∗
          (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗
          (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
          (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗
          (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st0 s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk msgLen 2 := ⟨⟨by omega, hpow2, by omega⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  obtain ⟨hf0, hf1, hf2, hf3, hstep_chunk⟩ := fitsEvents_encodeBytesAllocChunk hfits
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc_raw : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem halloc_sat
  have halloc := subroutine_ok_allocNoOomWithStack_of_budget (stk := allocHookStack) halloc_raw
  simp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  simp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat, Bool.false_eq_true, ↓reduceIte] at halloc
  let st1 := M.stepEvents (rustAllocEvents msgLen 2) st0
  let st2 := M.stepEvents (rustAllocEvents msgLen 2) st1
  let st3 := M.stepEvents (rustAllocEvents msgLen 2) st2
  have hsp_align : s.spAligned = true := by simpa [State.spAligned, hsp] using hfsp_align
  wp_norm_hyp hpc; wp_norm_hyp hsp_align; wp_norm_hyp hx21
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 384#64)
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st0)
  have htr8 := (‹Heap.AllocCallPreserved _ sf_1›).2.1
  have hoom8 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st1)
  have htr9 := (‹Heap.AllocCallPreserved _ sf_3›).2.1
  have hoom9 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st2)
  have htr10 := (‹Heap.AllocCallPreserved _ sf_5›).2.1
  have hoom10 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st3)
  have htr11 := (‹Heap.AllocCallPreserved _ sf_7›).2.1
  have hoom11 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
  wp_steps_sync_pool ((blkPl_417).base + 384#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rw [hstep_chunk]
  refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
    hoom8 hoom9 hoom10 hoom11 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [arm64_norm, wp_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [arm64_norm, wp_norm, *]

set_option maxHeartbeats 800000 in
theorem encode_bytes_alloc_12_15_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    {Q Qp : State → SepProp → Prop}
    (hshim_sat : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc_sat : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (s0 s : State) (st0 : M.σ) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (hfits : FitsEvents M lim st0 (encodeBytesAllocChunkEvents msgLen))
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 384#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ s4 (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0 → p13 ≠ 0 → p14 ≠ 0 → p15 ≠ 0 →
      s4.pc = (blkPl_417).base + 476#64 → s4.status = .Running → s4.sp = fsp →
      s4.readReg64 .x19 = s.readReg64 .x19 → s4.readReg64 .x20 = s.readReg64 .x20 →
      s4.readReg64 .x21 = BitVec.ofNat 64 msgLen →
      s4.readReg64 .x23 = s.readReg64 .x23 → s4.readReg64 .x24 = s.readReg64 .x24 →
      s4.readReg64 .x25 = s.readReg64 .x25 → s4.readReg64 .x26 = s.readReg64 .x26 →
      s4.readReg64 .x27 = p12 → s4.readReg64 .x28 = p13 →
      s4.readReg64 .x22 = p14 → s4.readReg64 .x0 = p15 →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool lim (M.stepEvents (encodeBytesAllocChunkEvents msgLen) st0) s4 ∗
          (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗
          (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
          (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗
          (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st0 s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk msgLen 2 := ⟨⟨by omega, hpow2, by omega⟩, by omega⟩
  have hmsgLen_toNat : (BitVec.ofNat 64 msgLen).toNat = msgLen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  obtain ⟨hf0, hf1, hf2, hf3, hstep_chunk⟩ := fitsEvents_encodeBytesAllocChunk hfits
  have hshim : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) sessionShimBudgetSpec :=
    spqr_hook_ok_of_mem hshim_sat
  have halloc_raw : subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
    spqr_hook_ok_of_mem halloc_sat
  have halloc := subroutine_ok_allocNoOomWithStack_of_budget (stk := allocHookStack) halloc_raw
  simp only [sessionShimBudgetSpec, sessionShimSpec] at hshim
  simp only [rustAllocNoOomSpecWithStack, rustCliAllocNoOomSpecWithStack] at halloc
  dsimp only [Reg.x0, Reg.x1, BitVec.ofNat_eq_ofNat, Bool.false_eq_true, ↓reduceIte] at halloc
  let st1 := M.stepEvents (rustAllocEvents msgLen 2) st0
  let st2 := M.stepEvents (rustAllocEvents msgLen 2) st1
  let st3 := M.stepEvents (rustAllocEvents msgLen 2) st2
  have hsp_align : s.spAligned = true := by simpa [State.spAligned, hsp] using hfsp_align
  wp_norm_hyp hpc; wp_norm_hyp hsp_align; wp_norm_hyp hx21
  apply SepWPp.of_sepWP (mid := (blkPl_417).base + 476#64)
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st0)
  have htr12 := (‹Heap.AllocCallPreserved _ sf_1›).2.1
  have hoom12 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st1)
  have htr13 := (‹Heap.AllocCallPreserved _ sf_3›).2.1
  have hoom13 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st2)
  have htr14 := (‹Heap.AllocCallPreserved _ sf_5›).2.1
  have hoom14 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  wp_call halloc (msgLen, 2, st3)
  have htr15 := (‹Heap.AllocCallPreserved _ sf_7›).2.1
  have hoom15 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
  wp_steps_sync_pool ((blkPl_417).base + 476#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rw [hstep_chunk]
  refine SepWPp.weaken_pre ?_ (hcont _ (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
    hoom12 hoom13 hoom14 hoom15 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · simp only [arm64_norm, wp_norm]
    exact Entails.of_eq (by sep_ac_rfl)
  all_goals simp only [arm64_norm, wp_norm, *]

/-! ## `VmPreserved`-Strengthened Stack Header Initialization (Block `417`) -/

theorem encode_bytes_store_headers_empty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 496#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = 0#64)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 668#64) s (memRegion (fsp + 72#64) 384 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) (List.replicate 16 ⟨0#64, 2#64⟩)
          (List.replicate 16 { value := [] }) ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_store_headers_empty_placed
      (A := A) (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp hfsp_align Frame
      hpc hrun hsp (by simpa using hx21) htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx19_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx19_m, htr_m, hvr_m⟩

theorem encode_bytes_store_headers_nonempty_placed {A : RustAlloc}
    {ext : String → Option (State → State)} (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (msgLen : Nat) (heven : msgLen % 2 = 0) (hpos : 2 ≤ msgLen) (hle : msgLen ≤ 1048576)
    (v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0) (hp2 : p2 ≠ 0) (hp3 : p3 ≠ 0)
    (hp4 : p4 ≠ 0) (hp5 : p5 ≠ 0) (hp6 : p6 ≠ 0) (hp7 : p7 ≠ 0)
    (hp8 : p8 ≠ 0) (hp9 : p9 ≠ 0) (hp10 : p10 ≠ 0) (hp11 : p11 ≠ 0)
    (hp12 : p12 ≠ 0) (hp13 : p13 ≠ 0) (hp14 : p14 ≠ 0) (hp15 : p15 ≠ 0)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_417).base + 476#64) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 msgLen)
    (hx23 : s.readReg64 .x23 = p8) (hx24 : s.readReg64 .x24 = p9)
    (hx25 : s.readReg64 .x25 = p10) (hx26 : s.readReg64 .x26 = p11)
    (hx27 : s.readReg64 .x27 = p12) (hx28 : s.readReg64 .x28 = p13)
    (hx22 : s.readReg64 .x22 = p14) (hx0 : s.readReg64 .x0 = p15)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    let cap := BitVec.ofNat 64 (msgLen / 2)
    let pins : List VecPin :=
      [⟨cap, p0⟩, ⟨cap, p1⟩, ⟨cap, p2⟩, ⟨cap, p3⟩, ⟨cap, p4⟩, ⟨cap, p5⟩, ⟨cap, p6⟩, ⟨cap, p7⟩,
       ⟨cap, p8⟩, ⟨cap, p9⟩, ⟨cap, p10⟩, ⟨cap, p11⟩, ⟨cap, p12⟩, ⟨cap, p13⟩, ⟨cap, p14⟩, ⟨cap, p15⟩]
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      ((blkPl_417).base + 724#64) s
      (memRegion (fsp + 72#64) 384 ∗ (fsp ↦₆₄ v0) ∗
        ((fsp + 8#64) ↦₆₄ p7) ∗ ((fsp + 16#64) ↦₆₄ p6) ∗
        ((fsp + 24#64) ↦₆₄ p5) ∗ ((fsp + 32#64) ↦₆₄ p4) ∗
        ((fsp + 40#64) ↦₆₄ p3) ∗ ((fsp + 48#64) ↦₆₄ p2) ∗
        ((fsp + 56#64) ↦₆₄ p1) ∗ ((fsp + 64#64) ↦₆₄ p0) ∗
        (A.live p0 msgLen 2 ∗ memRegion p0 msgLen) ∗ (A.live p1 msgLen 2 ∗ memRegion p1 msgLen) ∗
        (A.live p2 msgLen 2 ∗ memRegion p2 msgLen) ∗ (A.live p3 msgLen 2 ∗ memRegion p3 msgLen) ∗
        (A.live p4 msgLen 2 ∗ memRegion p4 msgLen) ∗ (A.live p5 msgLen 2 ∗ memRegion p5 msgLen) ∗
        (A.live p6 msgLen 2 ∗ memRegion p6 msgLen) ∗ (A.live p7 msgLen 2 ∗ memRegion p7 msgLen) ∗
        (A.live p8 msgLen 2 ∗ memRegion p8 msgLen) ∗ (A.live p9 msgLen 2 ∗ memRegion p9 msgLen) ∗
        (A.live p10 msgLen 2 ∗ memRegion p10 msgLen) ∗ (A.live p11 msgLen 2 ∗ memRegion p11 msgLen) ∗
        (A.live p12 msgLen 2 ∗ memRegion p12 msgLen) ∗ (A.live p13 msgLen 2 ∗ memRegion p13 msgLen) ∗
        (A.live p14 msgLen 2 ∗ memRegion p14 msgLen) ∗ (A.live p15 msgLen 2 ∗ memRegion p15 msgLen) ∗
        Frame)
      (fun sm Pm =>
        (Pm ⊢ pointListPinAt A (fsp + 72#64) pins (List.replicate 16 { value := [] }) ∗
          cells fsp 9 ∗ Frame) ∧
        VmPreserved s sm ∧
        sm.sp = fsp ∧ sm.readReg64 .x8 = BitVec.ofNat 64 msgLen - 2#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0) := by
  intro cap pins
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_store_headers_nonempty_placed
      (A := A) (ext := vmTrapHooks) s0 (ProofLib.stripS keep417 s) fsp hfsp_align
      msgLen heven hpos hle v0 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
      hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15 Frame
      hpc hrun hsp (by simpa using hx21)
      (by simpa using hx23) (by simpa using hx24) (by simpa using hx25) (by simpa using hx26)
      (by simpa using hx27) (by simpa using hx28) (by simpa using hx22) (by simpa using hx0)
      htrace hvregs)
    fun sm Pm hvm ⟨hPm, hsp_m, hx8_m, hx19_m, hx20_m, htr_m, hvr_m⟩ =>
      ⟨hPm, hvm, hsp_m, by simpa using hx8_m, by simpa using hx19_m, by simpa using hx20_m,
        htr_m, hvr_m⟩

end Placed

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.AllocBudget
