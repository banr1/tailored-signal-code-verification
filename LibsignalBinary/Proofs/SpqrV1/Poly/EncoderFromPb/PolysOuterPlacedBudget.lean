/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget
import LibsignalBinary.Heap.IfaceSimp
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuter
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.polys` Outer Loop for `<PolyEncoder>::from_pb`

Threads `RustCliAllocBudget M`, `encoderFromPbPolysLoopEvents`, `VmPreserved`, and
`AllocCallPreserved` through the `.polys` element steps and 16-slot outer loop (`+1204..+1548`) on
Block `374`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkLib_374 blkLib_eq_374 blkPC_374 blkPl_374 lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 PolynomialError)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecAt vecBuf vecHeader vecOf vecU8)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Drop (vecGF16ListOf vecGF16Of)
open CryptoVerification.SpqrV1.Poly (gf16Align gf16At gf16Stride)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  add_neg_16_eq_sub_16 add_neg_24_eq_sub_24 add_neg_32_eq_sub_32
  add_neg_48_eq_sub_48 add_neg_64_eq_sub_64
  beq_false_of_gt beq_false_of_lt
  bit0_and_32_eq_one_of_odd_63 bit0_and_32_eq_zero_of_even_63
  bit0_and_64_eq_one_of_odd_63 bit0_and_64_eq_zero_of_even_63
  bne_of_gt bne_of_lt bv_add_lit_add_lit bv_lit_add_lit
  bytesToGF16ListTotal bytesToGF16ListTotal_length
  cells_864_eq cells_896_eq cmn_one_bne_zero cmn_one_ne_zero
  decodePbPolysTotal extractLsb56_shiftedWord7
  fsp_864_add_23 fsp_864_add_7 fsp_864_after_write_rest fsp_864_split_at_7_rest
  fsp_880_after_write_rest fsp_880_split_at_7_rest fsp_896_add_16 fsp_896_add_9
  fsp_904_split_at_1_rest
  fsp_928_sub_16 fsp_928_sub_24 fsp_928_sub_32 fsp_928_sub_48 fsp_928_sub_64
  madd_24_eq midWord1 midWord7_midWord1_shiftedWord7 mul_24_eq
  neg_one_beq_false neg_one_beq_false' ofNat_beq_zero_false_of_pos ofNat_ne_zero_of_pos
  ofNat_succ_add_neg_one ofNat_succ_sub_one polyDeserializeTotal
  shiftRight_1_eq_div_2_63 shiftRight_1_nat_eq_div_2_63 shiftedWord7
  slot_after_write_rest slot_split_at_1_rest spqrRustDeallocSym
  vecGF16ListOf_append vecU8Rest vecU8Rest_entails_len_lt vecU8_close vecU8_open
  zeroExtend_setWidth32_setWidth8 zeroPolySlotAt zeroPolySlotsAt
  zeroPolySlotsAt_entails_vecGF16ListOf
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm sepWPp_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  encoderFromPbPolysLoopEvents encoderFromPbPolysSlotEvents
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget (
  polys_inner_loop_placed
)

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit
  ofNat_succ_sub_one ofNat_succ_add_neg_one zeroExtend_setWidth32_setWidth8
  add_neg_64_eq_sub_64 add_neg_48_eq_sub_48 add_neg_32_eq_sub_32
  add_neg_24_eq_sub_24 add_neg_16_eq_sub_16
  fsp_928_sub_64 fsp_928_sub_48 fsp_928_sub_32 fsp_928_sub_24 fsp_928_sub_16
  fsp_896_add_9 fsp_896_add_16 fsp_864_add_7 fsp_864_add_23
  madd_24_eq mul_24_eq

private theorem seq_vm_wpp {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid ret : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q_mid : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q_mid sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q_mid sm →
      SepWPp (P.rebase b Hk) ret sm P_mid Q Qp) :
    SepWPp (P.rebase b Hk) ret s Pre Q Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQm⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hvm hQm))

private theorem transport_pool_auto {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {s1 s2 : State}
    {prog : Program} {target_pc : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (hvm : VmPreserved s1 s2 := by assumption)
    (hnext : SepWP prog target_pc s2 (A.pool lim st s2 ∗ F) post) :
    SepWP prog target_pc s2 P post :=
  ProofLib.SepWP.transport_budgetPool hvm hf hnext

private theorem hchk_374 : VerifiedLibraries.RustStd.checkBlockNoSvc0 (blkLib_374).text = true := rfl

private theorem hisProg_374 [LibsignalPlacement] (H : CryptoVerification.LibsignalHooks) :
    CryptoVerification.IsLsBlockProg ((blkPC_374).rebase (blkPl_374).base H) 374 H := inferInstance

local macro "wp_steps_374" ext:ident mid:term : tactic => `(tactic| (
  apply @sepWP_seg_ls_vm _ _ _ _ 374 (Rust.withPanics $ext)
    (hisProg_374 _) (hisProg_374 _) blkLib_eq_374 hchk_374 $mid
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

private theorem align_pre_dep {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid s)
    (hwp : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem sepWPp_seq_clean_dep {prog : Program} {mid ret : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    {post Qp : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWPp prog ret sm (P_mid sm) post Qp) :
    SepWPp prog ret s Pre post Qp :=
  SepWPp.of_sepWP (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hent, hQm⟩ =>
    SepWPp.weaken_pre hent (h2 sm hpc hrun hQm))

private theorem bind_wpp_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : let s_mid := s; SepWPp prog ret s_mid P Q Qp) :
    SepWPp prog ret s P Q Qp := h

private theorem peel_fits {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {e1 e2 : List AllocEvent} (h : FitsEvents M lim st (e1 ++ e2)) :
    FitsEvents M lim st e1 ∧ FitsEvents M lim (M.stepEvents e1 st) e2 :=
  (fitsEvents_append M lim e1 e2 st).mp h

private theorem encoderFromPbPolysLoopEvents_cons_nil {rest : List (List (BitVec 8))} :
    encoderFromPbPolysLoopEvents ([] :: rest) = [] := by
  simp [encoderFromPbPolysLoopEvents, List.takeWhile]

private theorem encoderFromPbPolysLoopEvents_cons_odd {bs : List (BitVec 8)}
    {rest : List (List (BitVec 8))} (hodd : (bs.length % 2 != 0) = true) :
    encoderFromPbPolysLoopEvents (bs :: rest) = [] := by
  have hbeq : (bs.length % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact bne_iff_ne.mp hodd
  simp [encoderFromPbPolysLoopEvents, List.takeWhile, hbeq]

private theorem encoderFromPbPolysLoopEvents_cons_valid {b0 : BitVec 8} {bs' : List (BitVec 8)}
    {rest : List (List (BitVec 8))} (heven : (b0 :: bs').length % 2 = 0) :
    encoderFromPbPolysLoopEvents ((b0 :: bs') :: rest) =
      encoderFromPbPolysSlotEvents (b0 :: bs') ++ encoderFromPbPolysLoopEvents rest := by
  have hbeq : ((b0 :: bs').length % 2 == 0) = true := beq_iff_eq.mpr heven
  simp only [List.length_cons] at hbeq
  simp [encoderFromPbPolysLoopEvents, List.takeWhile, hbeq]

/-- Placed empty-slice error step (`+1204 -> +1496`) when `bs = []`, preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem polys_elem_empty_step_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (j : Nat) (s : State) (fsp polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * j)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 1496#64)
      s
      (((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = 2#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  by_vm_steps (
    wp_steps
    wp_done
  )

/-- Placed odd-length error step (`+1204 -> +1496`) when `bs.length % 2 ≠ 0`, preserving
    `VmPreserved` and `AllocCallPreserved`. -/
theorem polys_elem_odd_step_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (j : Nat) (bs : List (BitVec 8)) (s : State) (fsp polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hodd : bs.length % 2 ≠ 0) (hmax : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_374).base + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * j)) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 1496#64)
      s
      (((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x19 = 2#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hbit32 := bit0_and_32_eq_one_of_odd_63 hodd hmax
  have hbit64 := bit0_and_64_eq_one_of_odd_63 hodd hmax
  by_vm_steps (
    wp_steps
    wp_done
  )

/-- Placed non-empty even-slice step (`+1204 -> +1356`) when `bs.length = 2 * (m + 1)` under
    `FitsEvents M lim st (rustAllocEvents bs.length 2)`. -/
theorem polys_elem_even_nonempty_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (j m : Nat) (bs : List (BitVec 8)) (st : M.σ)
    (hFit : FitsEvents M lim st (rustAllocEvents bs.length 2))
    (s0 s : State) (fsp polysPtr bsPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hlen : bs.length = 2 * (m + 1)) (hmax : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_374).base + 1204#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = fsp + 864#64)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * j))
    (hx29 : s.readReg64 .x29 = fsp + 928#64)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (outPtr : BitVec 64),
      outPtr ≠ 0#64 →
      sm.pc = (blkPl_374).base + 1356#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      sm.readReg64 .x22 = BitVec.ofNat 64 j →
      sm.readReg64 .x23 = fsp + 864#64 →
      sm.readReg64 .x24 = polysPtr →
      sm.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)) →
      sm.readReg64 .x29 = fsp + 928#64 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (bsPtr ↦ₛ bs) ∗
          ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
          ((fsp + 904#64) ↦₆₄ outPtr) ∗
          ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
          vecBuf A.repAlloc 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) ∗
          A.pool lim (M.stepEvents (rustAllocEvents bs.length 2) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
        ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bsPtr ↦ₛ bs) ∗
        cells (fsp + 896#64) 3 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have heven : bs.length % 2 = 0 := by omega
  have hpos : 0 < bs.length := by omega
  have hn64 : bs.length < 2 ^ 64 := by omega
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk bs.length 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbit32 := bit0_and_32_eq_zero_of_even_63 heven hmax
  have hbit64 := bit0_and_64_eq_zero_of_even_63 heven hmax
  have hne0 := ofNat_ne_zero_of_pos hpos hn64
  have hbeq0 := ofNat_beq_zero_false_of_pos hpos hn64
  have hlsr1 : BitVec.ofNat 64 bs.length >>> 1#64 = BitVec.ofNat 64 (m + 1) := by
    rw [shiftRight_1_eq_div_2_63 hmax]; congr 1; omega
  have hlsr2 : BitVec.ofNat 64 bs.length >>> 1 = BitVec.ofNat 64 (m + 1) := by
    rw [shiftRight_1_nat_eq_div_2_63 hmax]; congr 1; omega
  have hlen_fn : True → bs.length = 2 * (m + 1) := fun _ => hlen
  clear hlen
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  clear halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  apply SepWPp.of_sepWP (mid := (blkPl_374).base + 1244#64)
  wp_steps_374 ext (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_apply
  refine transport_pool_auto (hnext := ?_)
  wp_steps_374 ext (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_oom : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have hacp1 : AllocCallPreserved s0 sf_1 :=
    (hacp.trans (by have h := ‹AllocCallPreserved _ sf›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_1›; simpa only [arm64_norm, wp_norm] using h)
  have htr0 : sf_1.trace = s0.trace := hacp1.2.1
  rw [cells_896_eq fsp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v1
  apply SepWPp.exists_elim; intro v2
  apply @sepWPp_seg_ls_vm _ _ _ _ 374 (Rust.withPanics ext)
    (hisProg_374 _) (hisProg_374 _) blkLib_eq_374 hchk_374 ((blkPl_374).base + 1308#64)
  intro m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun m_real hnsp => ?_
  refine ProofLib.SepWPp.transport_budgetPool
    (hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply bind_wpp_state; intro s_mid
  have hlen := hlen_fn trivial
  set outPtr := sf_1.readReg64 (Reg.gpr 0#5)
  have hacp2 : AllocCallPreserved s0 s_mid := by
    dsimp only [s_mid]; simpa only [arm64_norm, wp_norm] using hacp1
  refine SepWPp.weaken_pre
    (by
      dsimp only [s_mid, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      simp only [BitVec.add_zero, arm64_norm, wp_norm, *]
      exact Entails.of_eq (by sep_ac_rfl))
    (seq_vm_wpp
      (polys_inner_loop_placed (ext := ext) m bs 0 (m + 1) s_mid fsp bsPtr outPtr 0#64 hfsp_align
        (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((fsp + 904#64) ↦₆₄ outPtr) ∗
          A.live outPtr bs.length 2 ∗
          A.pool lim (M.stepEvents (rustAllocEvents bs.length 2) st) s_mid ∗
          stackAt fsp allocHookStack ∗ Frame)
        hlen (by omega) (by omega)
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x0, outPtr, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x19, *])
        (by rw [← hlen]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x21, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x26, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x27, *])
        (by dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x29, *]))
      ?_)
  intro s3 hpc3 hrun3 hvm3 ⟨hsp3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx28_3, hx29_3, htr3, hacp23, hvregs3⟩
  rw [← A.pool_of_vmPreserved hvm3]
  have hj_step : BitVec.ofNat 64 (24 * j + 24) = BitVec.ofNat 64 (24 * (j + 1)) := rfl
  refine SepWPp.weaken_pre ?_
    (hcont s3 outPtr hoom hpc3 hrun3 hsp3
      (by rw [hx20_3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by rw [hx22_3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x22, *])
      (by rw [hx23_3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x23, *])
      (by rw [hx24_3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x24, *])
      (by rw [hx28_3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, Reg.x28, hj_step, *])
      hx29_3
      (by rw [htr3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, htr0, *])
      (hacp2.trans hacp23)
      (by rw [hvregs3]; dsimp only [s_mid]; simp only [arm64_norm, wp_norm, *]))
  have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
  have hm64 : m + 1 < 2 ^ 64 := by omega
  have hcap_toNat : (BitVec.ofNat 64 (m + 1)).toNat = m + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64]
  have hcap_ne : BitVec.ofNat 64 (m + 1) ≠ 0 := ofNat_ne_zero_of_pos (by omega) hm64
  dsimp only [Nat.mul_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat]
  simp only [BitVec.add_zero]
  refine Entails.trans
    (Entails.of_eq (show _ =
      (A.repAlloc.live outPtr bs.length 2 ∗
       arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs)) ∗
      (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
       ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
       (bsPtr ↦ₛ bs) ∗
       ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
       ((fsp + 904#64) ↦₆₄ outPtr) ∗
       ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
       A.pool lim (M.stepEvents (rustAllocEvents bs.length 2) st) s3 ∗
       stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_left
      (show A.repAlloc.live outPtr bs.length 2 ∗ arrayAt gf16At 2 outPtr (bytesToGF16ListTotal bs) ⊢
        vecBuf A.repAlloc 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) by
        unfold vecBuf
        rw [hpts_len, hcap_toNat]
        simp only [hcap_ne, ↓reduceIte, Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp]
        have hm2 : (m + 1) * 2 = bs.length := by omega
        rw [hm2]
        exact Entails.pure_right ⟨by omega, by omega, hoom⟩ (Entails.of_eq (by sep_ac_rfl))))
    (Entails.of_eq (by sep_ac_rfl))

/-- Placed finish a single `.polys` element (`+1356 -> if j + 1 < 16 then +1204 else +1548`),
    advancing `A.pool` by `rustDeallocEvents 2 2` and preserving `AllocCallPreserved`. -/
theorem polys_elem_finish_step_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (j m : Nat) (hj : j < 16) (hm : 2 * (m + 1) < 2 ^ 63)
    (bs : List (BitVec 8)) (hlen : bs.length = 2 * (m + 1))
    (st : M.σ) (s : State) (fsp polysPtr outPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 1356#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (j + 1))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 j)
    (hx23 : s.readReg64 .x23 = fsp + 864#64)
    (hx24 : s.readReg64 .x24 = polysPtr)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)))
    (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (if j + 1 < 16 then (blkPl_374).base + 1204#64
       else (blkPl_374).base + 1548#64)
      s
      (zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
        ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
        ((fsp + 904#64) ↦₆₄ outPtr) ∗
        ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
        vecBuf A.repAlloc 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs) ∗
        cells (fsp + 864#64) 4 ∗
        A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) ∗
          cells (fsp + 864#64) 4 ∗
          cells (fsp + 896#64) 3 ∗
          A.pool lim (M.stepEvents (rustDeallocEvents 2 2) st) sm ∗
          stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 (j + 1) ∧
        sm.readReg64 .x23 = fsp + 864#64 ∧
        sm.readReg64 .x24 = polysPtr ∧
        sm.readReg64 .x28 = BitVec.ofNat 64 (24 * (j + 1)) ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  simp only [rustCliDeallocBudgetSpec, BitVec.ofNat_eq_ofNat] at hdealloc
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hcmn1 := cmn_one_ne_zero (m := m) (by omega)
  have hcmn2 := cmn_one_bne_zero (m := m) (by omega)
  have hneg1 := neg_one_beq_false (m := m) (by omega)
  have hneg2 := neg_one_beq_false' (m := m) (by omega)
  have hmadd := madd_24_eq j (fsp + 480#64)
  unfold zeroPolySlotAt
  rw [cells_864_eq fsp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro u0
  apply ProofLib.SepWP.exists_left; intro u1
  apply ProofLib.SepWP.exists_left; intro u2
  apply ProofLib.SepWP.exists_left; intro u3
  apply ProofLib.SepWP.exists_left; intro oldPtr
  wp_simp_pre [sepConj_pure_left_comm]
  refine SepWP.weaken_pre (Entails.pure_left fun _ => Entails.refl _) ?_
  let slotAddr := fsp + 480#64 + BitVec.ofNat 64 (24 * j)
  let len := BitVec.ofNat 64 (m + 1)
  wp_simp_pre [sepConj_assoc]
  apply @sepWP_seg_ls_vm _ _ _ _ 374 (Rust.withPanics ext)
    (hisProg_374 _) (hisProg_374 _) blkLib_eq_374 hchk_374 (lsρ spqrRustDeallocSym)
  intro _m_strip
  wp_conv_pre => rw [fsp_904_split_at_1_rest fsp outPtr len]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step; wp_step
  wp_conv_pre => rw [← fsp_904_split_at_1_rest fsp outPtr len]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step
  wp_conv_pre => rw [fsp_864_split_at_7_rest fsp (midWord1 outPtr len) u1]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_conv_pre => rw [fsp_864_after_write_rest fsp outPtr len (u1.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step; wp_step
  wp_conv_pre => rw [fsp_880_split_at_7_rest fsp (midWord1 outPtr len) u3]; dsimp only [slotAddr, len]
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by wp_norm_lhs))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_apply
  have hacp_sf : AllocCallPreserved s sf := by
    have h := ‹AllocCallPreserved _ sf›
    simpa only [arm64_norm, wp_norm] using h
  have htr_sf : sf.trace = s.trace := hacp_sf.2.1
  wp_simp_pre [arm64_norm, wp_norm, hsp]
  apply @sepWP_seg_ls_vm _ _ _ _ 374 (Rust.withPanics ext)
    (hisProg_374 _) (hisProg_374 _) blkLib_eq_374 hchk_374
    (if j + 1 < 16 then (blkPl_374).base + 1204#64 else (blkPl_374).base + 1548#64)
  intro _m_strip2
  wp_step
  wp_conv_pre => rw [fsp_880_after_write_rest fsp outPtr len (u3.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step
  wp_conv_pre =>
    rw [fsp_880_split_at_7_rest fsp (midWord1 outPtr len) (shiftedWord7 len (u3.extractLsb' 56 8)),
        midWord7_midWord1_shiftedWord7, extractLsb56_shiftedWord7]
    dsimp only [slotAddr, len]
  wp_step
  wp_conv_pre => rw [fsp_880_after_write_rest fsp outPtr len (u3.extractLsb' 56 8)]; dsimp only [slotAddr, len]
  wp_step; wp_step; wp_step
  wp_conv_pre => rw [slot_split_at_1_rest slotAddr oldPtr 0#64]; dsimp only [slotAddr, len]
  wp_step; wp_step
  wp_conv_pre => rw [slot_after_write_rest slotAddr outPtr len 0#64]; dsimp only [slotAddr, len]
  wp_step
  have hpts_len := bytesToGF16ListTotal_length (m + 1) bs hlen
  by_cases hlt : j + 1 < 16
  · simp only [hlt, ↓reduceIte]
    have h24_lt : 24 * (j + 1) < 384 := by omega
    have hne384 : (BitVec.ofNat 64 (24 * (j + 1)) != 384#64) = true := bne_of_lt h24_lt (by decide)
    have hne384' : (384#64 != BitVec.ofNat 64 (24 * (j + 1))) = true := bne_of_gt h24_lt (by decide)
    have hbeq384 : (BitVec.ofNat 64 (24 * (j + 1)) == 384#64) = false := beq_false_of_lt h24_lt (by decide)
    have hbeq384' : (384#64 == BitVec.ofNat 64 (24 * (j + 1))) = false := beq_false_of_gt h24_lt (by decide)
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp2.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine align_pre_dep ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [hpts_len, cells_896_eq fsp]
      dsimp only [slotAddr, len, gf16Stride, gf16Align]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ outPtr) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           vecBuf A.repAlloc 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 864#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 872#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u1.extractLsb' 56 8)) ∗
           ((fsp + 880#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 888#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u3.extractLsb' 56 8))) ∗
          (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 904#64) ↦₆₄ outPtr) ∗
           ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1))) ∗
          (A.pool lim (M.stepEvents (rustDeallocEvents 2 2) st) _ ∗
           stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono_left ?_))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr (Entails.of_eq (by sep_ac_rfl)))
      · exact Entails.sepExists_right (midWord1 outPtr len)
          (Entails.sepExists_right (shiftedWord7 len (u1.extractLsb' 56 8))
            (Entails.sepExists_right (midWord1 outPtr len)
              (Entails.sepExists_right (shiftedWord7 len (u3.extractLsb' 56 8))
                (Entails.of_eq (by sep_ac_rfl)))))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr
          (Entails.sepExists_right len (Entails.of_eq (by sep_ac_rfl))))
    · refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by simpa only [arm64_norm, wp_norm] using hacp_sf,
        by wp_norm_goal⟩
  · simp only [hlt, ↓reduceIte]
    have hj15 : j = 15 := by omega
    subst hj15
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    refine ProofLib.SepWP.transport_budgetPool
      (_hnsp2.toVmPreserved (by wp_norm_lhs))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine align_pre_dep ?_ ?_
    · unfold vecGF16Of vecOf vecAt vecHeader
      rw [hpts_len, cells_896_eq fsp]
      dsimp only [slotAddr, len, gf16Stride, gf16Align]
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 480#64 + BitVec.ofNat 64 (24 * 15)) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * 15) + 8#64) ↦₆₄ outPtr) ∗
           ((fsp + 480#64 + BitVec.ofNat 64 (24 * 15) + 16#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           vecBuf A.repAlloc 2 2 gf16At (BitVec.ofNat 64 (m + 1)) outPtr (bytesToGF16ListTotal bs)) ∗
          (((fsp + 864#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 872#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u1.extractLsb' 56 8)) ∗
           ((fsp + 880#64) ↦₆₄ midWord1 outPtr (BitVec.ofNat 64 (m + 1))) ∗
           ((fsp + 888#64) ↦₆₄ shiftedWord7 (BitVec.ofNat 64 (m + 1)) (u3.extractLsb' 56 8))) ∗
          (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 (m + 1)) ∗
           ((fsp + 904#64) ↦₆₄ outPtr) ∗
           ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (m + 1))) ∗
          (A.pool lim (M.stepEvents (rustDeallocEvents 2 2) st) _ ∗
           stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      refine sepConj_mono ?_ (sepConj_mono ?_ (sepConj_mono_left ?_))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr (Entails.of_eq (by sep_ac_rfl)))
      · exact Entails.sepExists_right (midWord1 outPtr len)
          (Entails.sepExists_right (shiftedWord7 len (u1.extractLsb' 56 8))
            (Entails.sepExists_right (midWord1 outPtr len)
              (Entails.sepExists_right (shiftedWord7 len (u3.extractLsb' 56 8))
                (Entails.of_eq (by sep_ac_rfl)))))
      · exact Entails.sepExists_right len (Entails.sepExists_right outPtr
          (Entails.sepExists_right len (Entails.of_eq (by sep_ac_rfl))))
    · refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by simpa only [arm64_norm, wp_norm] using hacp_sf,
        by wp_norm_goal⟩

/-- Placed outer `.polys` deserialization loop (`+1204 -> +1496 / +1548`) under
    `FitsEvents M lim st (encoderFromPbPolysLoopEvents rem)` in `[LibsignalPlacement]`. -/
theorem polys_outer_loop_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (rustCliDeallocBudgetSpec M A lim))
    (s0 : State) (fsp polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rem : List (List (BitVec 8))) (j : Nat) (acc : List (List GF16))
      (st : M.σ) (s : State) (Frame : SepProp),
      FitsEvents M lim st (encoderFromPbPolysLoopEvents rem) →
      rem ≠ [] →
      j + rem.length = 16 →
      acc.length = j →
      s.pc = (blkPl_374).base + 1204#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x22 = BitVec.ofNat 64 j →
      s.readReg64 .x23 = fsp + 864#64 →
      s.readReg64 .x24 = polysPtr →
      s.readReg64 .x28 = BitVec.ofNat 64 (24 * j) →
      s.readReg64 .x29 = fsp + 928#64 →
      s.trace = s0.trace →
      AllocCallPreserved s0 s →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ sm (tail : List CryptoVerification.LibsignalSpqrV1.Poly),
        decodePbPolysTotal rem = .ok tail →
        sm.pc = (blkPl_374).base + 1548#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x29 = fsp + 928#64 →
        sm.trace = s0.trace →
        AllocCallPreserved s0 sm →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A.repAlloc (fsp + 480#64)
              (acc ++ tail.map CryptoVerification.LibsignalSpqrV1.Poly.coefficients) ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool lim (M.stepEvents (encoderFromPbPolysLoopEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame)
          Q Qp) →
      (∀ sm (errPolys : List (List GF16)),
        decodePbPolysTotal rem = .error .serializationInvalid →
        errPolys.length = 16 →
        sm.pc = (blkPl_374).base + 1496#64 →
        sm.status = .Running →
        sm.sp = fsp →
        sm.readReg64 .x19 = 2#64 →
        sm.readReg64 .x29 = fsp + 928#64 →
        sm.trace = s0.trace →
        AllocCallPreserved s0 sm →
        calleeSavedVRegs sm = calleeSavedVRegs s0 →
        SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
          (vecGF16ListOf A.repAlloc (fsp + 480#64) errPolys ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool lim (M.stepEvents (encoderFromPbPolysLoopEvents rem) st) sm ∗
            stackAt fsp allocHookStack ∗ Frame)
          Q Qp) →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
        (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) rem.length ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j)) rem ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp
  | [], _, _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => (hne rfl).elim
  | bs :: rest, j, acc, st, s, Frame, hFit, _, hj_rem, hacc_len, hpc, hrun, hsp,
    hx22, hx23, hx24, hx28, hx29, htrace, hacp, hvregs, hcont_ok, hcont_err => by
    have hj_lt : j < 16 := by simp only [List.length_cons] at hj_rem; omega
    dsimp only [List.length_cons, zeroPolySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_left (vecU8_open A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) bs))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWPp.exists_elim; intro cap
    apply SepWPp.exists_elim; intro bsPtr
    refine SepWPp.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
          (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
           zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
           zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (bsPtr ↦ₛ bs) ∗
           arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
           cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
           A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl))
        (Entails.trans
          (sepConj_mono_left (vecU8Rest_entails_len_lt A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs))
          (Entails.of_eq (show _ =
            ⌜bs.length < 2 ^ 63⌝ ∗
            (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
             zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
             zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
             arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
             cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
             A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)))) ?_
    apply SepWPp.pure_left; intro hbs_max
    cases bs with
    | nil =>
      have hdec_err : decodePbPolysTotal ([] :: rest) = .error .serializationInvalid := rfl
      have hevs_nil : encoderFromPbPolysLoopEvents ([] :: rest) = [] :=
        encoderFromPbPolysLoopEvents_cons_nil
      have hstep := polys_elem_empty_step_placed (ext := ext) j s fsp polysPtr hfsp_align
        (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ []) ∗
          vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr [] ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
        hpc hrun hsp hx24 hx28
      refine SepWPp.weaken_pre
        (by dsimp only [List.length_nil, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
        (seq_vm_wpp hstep ?_)
      intro sm hpcm hrunm hvmm ⟨hspm, hx19m, hx29m, htrm, hacpm, hvregsm⟩
      rw [← A.pool_of_vmPreserved hvmm]
      have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
        simp only [List.length_cons] at hj_rem
        rw [List.length_append, List.length_replicate, hacc_len]
        omega
      refine SepWPp.weaken_pre ?_
        (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
          hpcm hrunm hspm hx19m (hx29m.trans hx29) (htrm.trans htrace) (hacp.trans hacpm)
          (hvregsm.trans hvregs))
      rw [hevs_nil, AllocCostModel.stepEvents_nil]
      have heq_pre :
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
          vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
          zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
          zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
          ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
          (bsPtr ↦ₛ []) ∗
          vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr [] ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame =
          (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
           zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
          (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
           ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length) ∗
           (bsPtr ↦ₛ []) ∗
           vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr []) ∗
          arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
          cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
          A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame := by
        dsimp only [zeroPolySlotsAt, List.length_nil, BitVec.ofNat_eq_ofNat]
        sep_ac_rfl
      rw [heq_pre]
      have hslots := zeroPolySlotsAt_entails_vecGF16ListOf A.repAlloc (rest.length + 1)
        (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
      have happ := vecGF16ListOf_append A.repAlloc acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
      rw [hacc_len] at happ
      have hclose := vecU8_close A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr []
      dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
      refine Entails.trans
        (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
          (sepConj_mono_left hclose))
        (Entails.of_eq (by sep_ac_rfl))
    | cons b0 bs' =>
      set bs := b0 :: bs'
      have hbs_ne_zero : (bs.length == 0) = false := by simp [bs]
      by_cases hodd_bool : (bs.length % 2 != 0) = true
      · have hodd : bs.length % 2 ≠ 0 := bne_iff_ne.mp hodd_bool
        have hevs_odd : encoderFromPbPolysLoopEvents (bs :: rest) = [] :=
          encoderFromPbPolysLoopEvents_cons_odd hodd_bool
        have hdec_err : decodePbPolysTotal (bs :: rest) = .error .serializationInvalid := by
          have h1 : (bs.length % 2 == 1) = true := by rw [beq_iff_eq]; omega
          simp [decodePbPolysTotal, polyDeserializeTotal, h1]
        have hstep := polys_elem_odd_step_placed (ext := ext) j bs s fsp polysPtr hfsp_align
          (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
            zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
          hodd hbs_max hpc hrun hsp hx24 hx28
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (seq_vm_wpp hstep ?_)
        intro sm hpcm hrunm hvmm ⟨hspm, hx19m, hx29m, htrm, hacpm, hvregsm⟩
        rw [← A.pool_of_vmPreserved hvmm]
        have herr_len : (acc ++ List.replicate (rest.length + 1) ([] : List GF16)).length = 16 := by
          simp only [List.length_cons] at hj_rem
          rw [List.length_append, List.length_replicate, hacc_len]
          omega
        refine SepWPp.weaken_pre ?_
          (hcont_err sm (acc ++ List.replicate (rest.length + 1) []) hdec_err herr_len
            hpcm hrunm hspm hx19m (hx29m.trans hx29) (htrm.trans htrace) (hacp.trans hacpm)
            (hvregsm.trans hvregs))
        rw [hevs_odd, AllocCostModel.stepEvents_nil]
        have heq_pre :
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
            zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
            zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame =
            (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
             zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (rest.length + 1)) ∗
            (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
             ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
             (bsPtr ↦ₛ bs) ∗
             vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
            A.pool lim st sm ∗ stackAt fsp allocHookStack ∗ Frame := by
          dsimp only [zeroPolySlotsAt]
          sep_ac_rfl
        rw [heq_pre]
        have hslots := zeroPolySlotsAt_entails_vecGF16ListOf A.repAlloc (rest.length + 1)
          (fsp + 480#64 + BitVec.ofNat 64 (24 * j))
        have happ := vecGF16ListOf_append A.repAlloc acc (List.replicate (rest.length + 1) []) (fsp + 480#64)
        rw [hacc_len] at happ
        have hclose := vecU8_close A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
        dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hslots) (Entails.of_eq happ.symm))
            (sepConj_mono_left hclose))
          (Entails.of_eq (by sep_ac_rfl))
      · have heven : bs.length % 2 = 0 := by
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at hodd_bool
          exact hodd_bool
        have hevs_cons : encoderFromPbPolysLoopEvents (bs :: rest) =
            encoderFromPbPolysSlotEvents bs ++ encoderFromPbPolysLoopEvents rest :=
          encoderFromPbPolysLoopEvents_cons_valid heven
        have hFit' : FitsEvents M lim st
            (encoderFromPbPolysSlotEvents bs ++ encoderFromPbPolysLoopEvents rest) := by
          rwa [← hevs_cons]
        rcases (peel_fits hFit') with ⟨hfit_slot, hfit_rest⟩
        rcases (peel_fits hfit_slot) with ⟨hfit_alloc, _⟩
        have hst_slot : M.stepEvents (rustDeallocEvents 2 2)
            (M.stepEvents (rustAllocEvents bs.length 2) st) =
            M.stepEvents (encoderFromPbPolysSlotEvents bs) st := by
          simp only [encoderFromPbPolysSlotEvents, AllocCostModel.stepEvents_append]
        set m := bs.length / 2 - 1
        have hlen_m : bs.length = 2 * (m + 1) := by
          have hpos : 0 < bs.length := by simp [bs]
          omega
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (polys_elem_even_nonempty_step_placed hshim halloc j m bs st hfit_alloc
            s0 s fsp polysPtr bsPtr hfsp_align
            (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
              zeroPolySlotAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) ∗
              zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
              vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
              arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
              cells (fsp + 864#64) 4 ∗ Frame)
            hlen_m hbs_max hpc hrun hsp hx22 hx23 hx24 hx28 hx29 htrace hacp hvregs ?_)
        intro s1 outPtr houtPtr hpc1 hrun1 hsp1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 hx29_1 htr1 hacp1 hvregs1
        have hfin := polys_elem_finish_step_placed (A := A) (ext := ext) hdealloc j m hj_lt
          (by omega) bs hlen_m (M.stepEvents (rustAllocEvents bs.length 2) st) s1 fsp polysPtr outPtr hfsp_align
          (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
            ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            (bsPtr ↦ₛ bs) ∗
            vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs ∗
            vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
            zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) rest.length ∗
            arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) rest ∗
            Frame)
          hpc1 hrun1 hsp1 hx20_1 hx22_1 hx23_1 hx24_1 hx28_1 hx29_1
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (sepWPp_seq_clean_dep hfin ?_)
        intro s2 hpc2 hrun2 ⟨hsp2, hx22_2, hx23_2, hx24_2, hx28_2, hx29_2, htr2, hacp12, hvregs2⟩
        rw [hst_slot]
        have hclose := vecU8_close A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs
        have happ := vecGF16ListOf_append A.repAlloc acc [bytesToGF16ListTotal bs] (fsp + 480#64)
        rw [hacc_len] at happ
        have hsingle : vecGF16ListOf A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) [bytesToGF16ListTotal bs] =
            vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs) := by
          dsimp only [vecGF16ListOf, arrayAt]; simp only [sepConj_emp]
        rw [hsingle] at happ
        have hpoly_ok : polyDeserializeTotal bs = .ok { coefficients := bytesToGF16ListTotal bs } := by
          have h1 : bs.isEmpty = false := rfl
          have h2 : (bs.length % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
          simp [polyDeserializeTotal, h1, h2]
        cases rest with
        | nil =>
          have hj15 : j = 15 := by simp only [List.length_cons, List.length_nil] at hj_rem; omega
          have hlt_false : ¬(j + 1 < 16) := by omega
          simp only [hlt_false, ↓reduceIte] at hpc2
          have hdec_ok : decodePbPolysTotal [bs] = .ok [{ coefficients := bytesToGF16ListTotal bs }] := by
            simp [decodePbPolysTotal, hpoly_ok]
          have hevs_one : encoderFromPbPolysLoopEvents [bs] = encoderFromPbPolysSlotEvents bs := by
            rw [hevs_cons]; simp [encoderFromPbPolysLoopEvents]
          refine SepWPp.weaken_pre ?_
            (hcont_ok s2 [{ coefficients := bytesToGF16ListTotal bs }] hdec_ok hpc2 hrun2 hsp2
              hx29_2 (htr2.trans htr1) (hacp1.trans hacp12) (hvregs2.trans hvregs1))
          rw [hevs_one]
          dsimp only [List.map, List.length_nil, zeroPolySlotsAt, arrayAt, BitVec.ofNat_eq_ofNat]
          simp only [sepConj_emp]
          refine Entails.trans
            (Entails.of_eq (show _ =
              (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
               vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
              (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
               ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
               (bsPtr ↦ₛ bs) ∗
               vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
              cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
              A.pool lim (M.stepEvents (encoderFromPbPolysSlotEvents bs) st) s2 ∗
              stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl)) ?_
          exact Entails.trans
            (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
            (Entails.of_eq (by sep_ac_rfl))
        | cons bs2 rest' =>
          have hlt_true : j + 1 < 16 := by simp only [List.length_cons] at hj_rem; omega
          simp only [hlt_true, ↓reduceIte] at hpc2
          have hj_addr1 : fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64 =
              fsp + 480#64 + BitVec.ofNat 64 (24 * (j + 1)) := by
            rw [bv_add_lit_add_lit]; rfl
          have hj_addr2 : polysPtr + BitVec.ofNat 64 (24 * j) + 24#64 =
              polysPtr + BitVec.ofNat 64 (24 * (j + 1)) := by
            rw [bv_add_lit_add_lit]; rfl
          have hst_cons : M.stepEvents (encoderFromPbPolysLoopEvents (bs2 :: rest'))
              (M.stepEvents (encoderFromPbPolysSlotEvents bs) st) =
              M.stepEvents (encoderFromPbPolysLoopEvents (bs :: bs2 :: rest')) st := by
            simp only [hevs_cons, AllocCostModel.stepEvents_append]
          refine SepWPp.weaken_pre ?_
            (polys_outer_loop_placed hshim halloc hdealloc s0 fsp polysPtr hfsp_align
              (bs2 :: rest') (j + 1) (acc ++ [bytesToGF16ListTotal bs])
              (M.stepEvents (encoderFromPbPolysSlotEvents bs) st) s2
              (vecU8 A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) bs ∗ Frame)
              hfit_rest (List.cons_ne_nil _ _)
              (by simp only [List.length_cons] at hj_rem ⊢; omega)
              (by rw [List.length_append, hacc_len]; rfl)
              hpc2 hrun2 hsp2 hx22_2 hx23_2 hx24_2 hx28_2 hx29_2 (htr2.trans htr1)
              (hacp1.trans hacp12) (hvregs2.trans hvregs1)
              (fun sm tail hdec_tail hpcm hrunm hspm hx29m htrm hacpm hvregsm => ?_)
              (fun sm errPolys hdec_err herr_len hpcm hrunm hspm hx19m hx29m htrm hacpm hvregsm => ?_))
          · rw [← hj_addr1, ← hj_addr2]
            refine Entails.trans
              (Entails.of_eq (show _ =
                (vecGF16ListOf A.repAlloc (fsp + 480#64) acc ∗
                 vecGF16Of A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j)) (bytesToGF16ListTotal bs)) ∗
                (((polysPtr + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ bsPtr) ∗
                 ((polysPtr + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
                 (bsPtr ↦ₛ bs) ∗
                 vecU8Rest A.repAlloc (polysPtr + BitVec.ofNat 64 (24 * j)) cap bsPtr bs) ∗
                zeroPolySlotsAt A.repAlloc (fsp + 480#64 + BitVec.ofNat 64 (24 * j) + 24#64) (bs2 :: rest').length ∗
                arrayAt (fun bs addr => vecU8 A.repAlloc addr bs) 24 (polysPtr + BitVec.ofNat 64 (24 * j) + 24#64) (bs2 :: rest') ∗
                cells (fsp + 864#64) 4 ∗ cells (fsp + 896#64) 3 ∗
                A.pool lim (M.stepEvents (encoderFromPbPolysSlotEvents bs) st) s2 ∗
                stackAt fsp allocHookStack ∗ Frame by sep_ac_rfl)) ?_
            exact Entails.trans
              (sepConj_mono (Entails.of_eq happ.symm) (sepConj_mono_left hclose))
              (Entails.of_eq (by sep_ac_rfl))
          · have hdec_cons : decodePbPolysTotal (bs :: bs2 :: rest') =
                .ok ({ coefficients := bytesToGF16ListTotal bs } :: tail) := by
              change (match polyDeserializeTotal bs with
                | Except.error e => Except.error e
                | Except.ok p => match decodePbPolysTotal (bs2 :: rest') with
                  | Except.error e => Except.error e
                  | Except.ok tail => Except.ok (p :: tail)) = _
              simp only [hpoly_ok, hdec_tail]
            have happ_assoc :
                (acc ++ [bytesToGF16ListTotal bs]) ++ tail.map CryptoVerification.LibsignalSpqrV1.Poly.coefficients =
                acc ++ ({ coefficients := bytesToGF16ListTotal bs } :: tail).map
                  CryptoVerification.LibsignalSpqrV1.Poly.coefficients := by
              simp [List.append_assoc]
            rw [happ_assoc, hst_cons, ← hj_addr2]
            refine SepWPp.weaken_pre
              (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
              (hcont_ok sm ({ coefficients := bytesToGF16ListTotal bs } :: tail) hdec_cons
                hpcm hrunm hspm hx29m htrm hacpm hvregsm)
          · have hdec_cons : decodePbPolysTotal (bs :: bs2 :: rest') = .error .serializationInvalid := by
              change (match polyDeserializeTotal bs with
                | Except.error e => Except.error e
                | Except.ok p => match decodePbPolysTotal (bs2 :: rest') with
                  | Except.error e => Except.error e
                  | Except.ok tail => Except.ok (p :: tail)) = _
              simp only [hpoly_ok, hdec_err]
            rw [hst_cons, ← hj_addr2]
            refine SepWPp.weaken_pre
              (by dsimp only [arrayAt, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by sep_ac_rfl))
              (hcont_err sm errPolys hdec_cons herr_len
                hpcm hrunm hspm hx19m hx29m htrm hacpm hvregsm)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysOuterPlacedBudget
