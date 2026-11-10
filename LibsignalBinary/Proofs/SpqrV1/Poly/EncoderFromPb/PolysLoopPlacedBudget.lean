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
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoop
import LibsignalBinary.Heap.IfaceSimp
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PtsLoop
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.polys` Initialization and Inner Loop for `<PolyEncoder>::from_pb`

Threads `RustCliAllocBudget M`, `encoderFromPbPolysInitEvents`, `VmPreserved`, and
`AllocCallPreserved` through 16-slot `Poly::zero()` initialization (`+556..+1204`) and the inner
`GF16` deserialization loop (`+1308..+1356`) on Block `374`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalPlacement blkLib_374 blkLib_eq_374 blkPC_374 blkPl_374 lsρ)
open CryptoVerification.LibsignalSpqrV1 (GF16 u16FromBeBytes)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (gf16At)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (
  add_neg_16_eq_sub_16 add_neg_24_eq_sub_24 add_neg_32_eq_sub_32
  add_neg_48_eq_sub_48 add_neg_64_eq_sub_64
  beq_false_of_gt beq_false_of_lt bne_of_gt bne_of_lt
  bv_add_lit_add_lit bv_lit_add_lit bytesToGF16ListTotal
  fsp_928_sub_16 fsp_928_sub_24 fsp_928_sub_32 fsp_928_sub_48 fsp_928_sub_64
  memRegion_two_cons ofNat_add_two ofNat_succ_add_neg_one ofNat_succ_sub_one
  pointsToBytes_pair_cons rev16_pair_eq_u16FromBeBytes
  sepWP_cells_succ sepWP_cells_zero ule_false_of_lt ult_of_lt
  zeroExtend_setWidth32_setWidth8 zeroPolySlotAt zeroPolySlotAt_intro zeroPolySlotsAt
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
  RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm sepWPp_seg_ls_vm)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.DefsBudget (
  encoderFromPbPolysInitEvents
)

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_lit_add_lit ofNat_succ_sub_one
  ofNat_succ_add_neg_one zeroExtend_setWidth32_setWidth8
  add_neg_64_eq_sub_64 add_neg_48_eq_sub_48 add_neg_32_eq_sub_32
  add_neg_24_eq_sub_24 add_neg_16_eq_sub_16
  fsp_928_sub_64 fsp_928_sub_48 fsp_928_sub_32 fsp_928_sub_24 fsp_928_sub_16

/-- Four consecutive `(size = 2, align = 2)` `Poly::zero()` allocations (right-associated for
    `fitsEvents_append` peeling). -/
def polysAlloc4Events : List AllocEvent :=
  rustAllocEvents 2 2 ++ (rustAllocEvents 2 2 ++ (rustAllocEvents 2 2 ++ rustAllocEvents 2 2))

theorem encoderFromPbPolysInitEvents_eq :
    encoderFromPbPolysInitEvents =
      polysAlloc4Events ++ (polysAlloc4Events ++ (polysAlloc4Events ++ polysAlloc4Events)) := by
  simp only [encoderFromPbPolysInitEvents, polysAlloc4Events,
    List.replicate, List.flatten, List.append_eq, List.append_assoc, List.append_nil]

private theorem peel_fits {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {e1 e2 : List AllocEvent} (h : FitsEvents M lim st (e1 ++ e2)) :
    FitsEvents M lim st e1 ∧ FitsEvents M lim (M.stepEvents e1 st) e2 :=
  (fitsEvents_append M lim e1 e2 st).mp h

private theorem sepWP_map_post {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 : State → SepProp → Prop}
    (hwp : SepWP prog target s P Q1)
    (himp : ∀ sm Pm, Q1 sm Pm → Q2 sm Pm) :
    SepWP prog target s P Q2 :=
  SepWP.mono hwp fun sm Pm _ _ hQ1 => himp sm Pm hQ1

private theorem align_pre_vm {prog : Program} {target : BitVec 64} {s : State} {tp : BitVec 64}
    {P P_mid : SepProp} {Q : State → Prop}
    (hent : P ⊢ P_mid)
    (hwp : SepWP prog target s P_mid (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = tp ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.weaken_pre hent hwp

private theorem seq_vm_clean {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

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

private theorem sync_pool_reg {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {prog : Program} {target : BitVec 64}
    {s1 s2 : State} {P F : SepProp} {post : State → SepProp → Prop}
    (hf : P = A.pool lim st s1 ∗ F := by sep_focus)
    (heq : A.pool lim st s1 = A.pool lim st s2)
    (hnext : SepWP prog target s2 (A.pool lim st s2 ∗ F) post) :
    SepWP prog target s2 P post := by
  rw [hf, heq]; exact hnext

private theorem hchk_374 : VerifiedLibraries.RustStd.checkBlockNoSvc0 (blkLib_374).text = true := rfl

private theorem hisProg_374 [LibsignalPlacement] (H : CryptoVerification.LibsignalHooks) :
    CryptoVerification.IsLsBlockProg ((blkPC_374).rebase (blkPl_374).base H) 374 H := inferInstance

attribute [local irreducible] Obj.MultiPlacedLib.blockPlacement

variable [LibsignalPlacement]

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

local macro "wpp_steps_374" ext:ident mid:term : tactic => `(tactic| (
  apply @sepWPp_seg_ls_vm _ _ _ _ 374 (Rust.withPanics $ext)
    (hisProg_374 _) (hisProg_374 _) blkLib_eq_374 hchk_374 $mid
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

local macro "polys_alloc_budget_call" ext:ident mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps_374 $ext (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_apply
  refine transport_pool_auto (hnext := ?_)
  wp_steps
  refine sync_pool_reg (heq := by
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC]) (hnext := ?_)
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

local macro "polys_alloc_budget_call_reg" mid:term : tactic => `(tactic| (
  apply SepWPp.of_sepWP (mid := $mid)
  wp_steps
  refine sync_pool_reg (heq := by
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC]) (hnext := ?_)
  wp_apply
  refine transport_pool_auto (hnext := ?_)
  wp_steps
  refine sync_pool_reg (heq := by
    simp only [RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC]) (hnext := ?_)
  wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
))

theorem polys_alloc_0_3_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (hFit : FitsEvents M lim st polysAlloc4Events)
    (s0 s : State) (fsp out pbA : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p0 p1 p2 p3 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 →
      sm.pc = (blkPl_374).base + 656#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = p0 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
          A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
          A.pool lim (M.stepEvents polysAlloc4Events st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells (fsp + 32#64) 5 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk 2 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  clear halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  rcases (peel_fits hFit) with ⟨hfit0, hFit1⟩
  rcases (peel_fits hFit1) with ⟨hfit1, hFit2⟩
  rcases (peel_fits hFit2) with ⟨hfit2, hfit3⟩
  have hst4 : M.stepEvents (rustAllocEvents 2 2)
      (M.stepEvents (rustAllocEvents 2 2)
        (M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st))) =
      M.stepEvents polysAlloc4Events st := by
    simp only [polysAlloc4Events, AllocCostModel.stepEvents_append]
  have hc5 : cells (fsp + 32#64) 5 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3, ∃∗ c4,
        ((fsp + 32#64) ↦₆₄ c0) ∗ ((fsp + 40#64) ↦₆₄ c1) ∗ ((fsp + 48#64) ↦₆₄ c2) ∗
        ((fsp + 56#64) ↦₆₄ c3) ∗ ((fsp + 64#64) ↦₆₄ c4) := by
    have h1 : fsp + 32#64 + 8#64 = fsp + 40#64 := by bv_omega
    have h2 : fsp + 40#64 + 8#64 = fsp + 48#64 := by bv_omega
    have h3 : fsp + 48#64 + 8#64 = fsp + 56#64 := by bv_omega
    have h4 : fsp + 56#64 + 8#64 = fsp + 64#64 := by bv_omega
    rw [ProofLib.cells_succ, h1, ProofLib.cells_succ, h2, ProofLib.cells_succ, h3,
        ProofLib.cells_succ, h4, ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc5]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 5 (apply SepWPp.exists_elim; intro _)
  polys_alloc_budget_call ext ((blkPl_374).base + 576#64)
  have hoom0 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom0
  have hacp0 : AllocCallPreserved s0 sf_1 :=
    (hacp.trans (by have h := ‹AllocCallPreserved _ sf›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_1›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 600#64)
  have hoom1 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  have hacp1 : AllocCallPreserved s0 sf_3 :=
    (hacp0.trans (by have h := ‹AllocCallPreserved _ sf_2›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_3›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 624#64)
  have hoom2 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  have hacp2 : AllocCallPreserved s0 sf_5 :=
    (hacp1.trans (by have h := ‹AllocCallPreserved _ sf_4›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_5›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 648#64)
  have hoom3 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
  have hacp3 : AllocCallPreserved s0 sf_7 :=
    (hacp2.trans (by have h := ‹AllocCallPreserved _ sf_6›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_7›; simpa only [arm64_norm, wp_norm] using h)
  wpp_steps_374 ext ((blkPl_374).base + 656#64)
  simp only [State.setMem_setMem]
  refine SepWPp.weaken_pre
    (by simp only [hst4, arm64_norm, wp_norm, *]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
      (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
      hoom0 hoom1 hoom2 hoom3
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, hacp3.2.1])
      (by simp only [arm64_norm, wp_norm, hacp3])
      (by simp only [arm64_norm, wp_norm, *]))

theorem polys_alloc_4_7_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (hFit : FitsEvents M lim st polysAlloc4Events)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 656#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p4 p5 p6 p7 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 → p6 ≠ 0#64 → p7 ≠ 0#64 →
      sm.pc = (blkPl_374).base + 752#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
          A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
          A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
          A.pool lim (M.stepEvents polysAlloc4Events st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk 2 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  clear halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  rcases (peel_fits hFit) with ⟨hfit0, hFit1⟩
  rcases (peel_fits hFit1) with ⟨hfit1, hFit2⟩
  rcases (peel_fits hFit2) with ⟨hfit2, hfit3⟩
  have hst4 : M.stepEvents (rustAllocEvents 2 2)
      (M.stepEvents (rustAllocEvents 2 2)
        (M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st))) =
      M.stepEvents polysAlloc4Events st := by
    simp only [polysAlloc4Events, AllocCostModel.stepEvents_append]
  have hc4 : cells fsp 4 =
      ∃∗ c0, ∃∗ c1, ∃∗ c2, ∃∗ c3,
        (fsp ↦₆₄ c0) ∗ ((fsp + 8#64) ↦₆₄ c1) ∗ ((fsp + 16#64) ↦₆₄ c2) ∗ ((fsp + 24#64) ↦₆₄ c3) := by
    have h1 : fsp + 8#64 + 8#64 = fsp + 16#64 := by bv_omega
    have h2 : fsp + 16#64 + 8#64 = fsp + 24#64 := by bv_omega
    rw [ProofLib.cells_succ, ProofLib.cells_succ, h1, ProofLib.cells_succ, h2,
        ProofLib.cells_succ, ProofLib.cells_zero]
    simp only [sepExists_sepConj_right, sepConj_emp, sepConj_assoc]
  rw [hc4]; simp only [sepExists_sepConj_left, sepConj_assoc]
  iterate 4 (apply SepWPp.exists_elim; intro _)
  polys_alloc_budget_call ext ((blkPl_374).base + 672#64)
  have hoom4 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq4 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
  have hacp4 : AllocCallPreserved s0 sf_1 :=
    (hacp.trans (by have h := ‹AllocCallPreserved _ sf›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_1›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 696#64)
  have hoom5 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq5 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
  have hacp5 : AllocCallPreserved s0 sf_3 :=
    (hacp4.trans (by have h := ‹AllocCallPreserved _ sf_2›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_3›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 720#64)
  have hoom6 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq6 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
  have hacp6 : AllocCallPreserved s0 sf_5 :=
    (hacp5.trans (by have h := ‹AllocCallPreserved _ sf_4›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_5›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call ext ((blkPl_374).base + 744#64)
  have hoom7 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq7 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
  have hacp7 : AllocCallPreserved s0 sf_7 :=
    (hacp6.trans (by have h := ‹AllocCallPreserved _ sf_6›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_7›; simpa only [arm64_norm, wp_norm] using h)
  wpp_steps_374 ext ((blkPl_374).base + 752#64)
  simp only [State.setMem_setMem]
  refine SepWPp.weaken_pre
    (by simp only [hst4, arm64_norm, wp_norm, *]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
      (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
      hoom4 hoom5 hoom6 hoom7
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, hacp7.2.1])
      (by simp only [arm64_norm, wp_norm, hacp7])
      (by simp only [arm64_norm, wp_norm, *]))

theorem polys_alloc_8_11_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (hFit : FitsEvents M lim st polysAlloc4Events)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 752#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p8 p9 p10 p11 : BitVec 64),
      p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 → p11 ≠ 0#64 →
      sm.pc = (blkPl_374).base + 848#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x19 = p8 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = p9 → sm.readReg64 .x23 = p10 →
      sm.readReg64 .x24 = p11 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
          A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
          A.pool lim (M.stepEvents polysAlloc4Events st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk 2 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  clear halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  rcases (peel_fits hFit) with ⟨hfit0, hFit1⟩
  rcases (peel_fits hFit1) with ⟨hfit1, hFit2⟩
  rcases (peel_fits hFit2) with ⟨hfit2, hfit3⟩
  have hst4 : M.stepEvents (rustAllocEvents 2 2)
      (M.stepEvents (rustAllocEvents 2 2)
        (M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st))) =
      M.stepEvents polysAlloc4Events st := by
    simp only [polysAlloc4Events, AllocCostModel.stepEvents_append]
  polys_alloc_budget_call_reg ((blkPl_374).base + 768#64)
  have hoom8 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq8 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom8
  have hacp8 : AllocCallPreserved s0 sf_1 :=
    (hacp.trans (by have h := ‹AllocCallPreserved _ sf›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_1›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 792#64)
  have hoom9 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq9 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom9
  have hacp9 : AllocCallPreserved s0 sf_3 :=
    (hacp8.trans (by have h := ‹AllocCallPreserved _ sf_2›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_3›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 816#64)
  have hoom10 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq10 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom10
  have hacp10 : AllocCallPreserved s0 sf_5 :=
    (hacp9.trans (by have h := ‹AllocCallPreserved _ sf_4›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_5›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 840#64)
  have hoom11 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq11 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom11
  have hacp11 : AllocCallPreserved s0 sf_7 :=
    (hacp10.trans (by have h := ‹AllocCallPreserved _ sf_6›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_7›; simpa only [arm64_norm, wp_norm] using h)
  apply SepWPp.of_sepWP (mid := (blkPl_374).base + 848#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.weaken_pre
    (by simp only [hst4, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC, arm64_norm, wp_norm, *]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
      (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
      hoom8 hoom9 hoom10 hoom11
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x19, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, *]) (by simp only [arm64_norm, wp_norm, Reg.x21, *])
      (by simp only [arm64_norm, wp_norm, Reg.x23, *]) (by simp only [arm64_norm, wp_norm, Reg.x24, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, hacp11.2.1])
      (by simp only [arm64_norm, wp_norm, hacp11])
      (by simp only [arm64_norm, wp_norm, *]))

theorem polys_alloc_12_15_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (hFit : FitsEvents M lim st polysAlloc4Events)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 848#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm (p12 p13 p14 p15 : BitVec 64),
      p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      sm.pc = (blkPl_374).base + 940#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x0 = p15 → sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 → sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = p12 → sm.readReg64 .x26 = p13 →
      sm.readReg64 .x27 = p14 → sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
          A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗
          A.pool lim (M.stepEvents polysAlloc4Events st) sm ∗ stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hpow2 : ∃ k : Nat, 2 = 2 ^ k := ⟨1, rfl⟩
  have hlay : RustLayoutOk 2 2 := ⟨⟨by omega, hpow2, by omega⟩, by decide⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have halloc_no_oom : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget halloc
  clear halloc
  simp only [rustAllocShimVmSpec] at hshim
  simp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat] at halloc_no_oom
  rcases (peel_fits hFit) with ⟨hfit0, hFit1⟩
  rcases (peel_fits hFit1) with ⟨hfit1, hFit2⟩
  rcases (peel_fits hFit2) with ⟨hfit2, hfit3⟩
  have hst4 : M.stepEvents (rustAllocEvents 2 2)
      (M.stepEvents (rustAllocEvents 2 2)
        (M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st))) =
      M.stepEvents polysAlloc4Events st := by
    simp only [polysAlloc4Events, AllocCostModel.stepEvents_append]
  polys_alloc_budget_call_reg ((blkPl_374).base + 864#64)
  have hoom12 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq12 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom12
  have hacp12 : AllocCallPreserved s0 sf_1 :=
    (hacp.trans (by have h := ‹AllocCallPreserved _ sf›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_1›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 888#64)
  have hoom13 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq13 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom13
  have hacp13 : AllocCallPreserved s0 sf_3 :=
    (hacp12.trans (by have h := ‹AllocCallPreserved _ sf_2›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_3›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 912#64)
  have hoom14 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq14 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom14
  have hacp14 : AllocCallPreserved s0 sf_5 :=
    (hacp13.trans (by have h := ‹AllocCallPreserved _ sf_4›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_5›; simpa only [arm64_norm, wp_norm] using h)
  polys_alloc_budget_call_reg ((blkPl_374).base + 936#64)
  have hoom15 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq15 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom15
  have hacp15 : AllocCallPreserved s0 sf_7 :=
    (hacp14.trans (by have h := ‹AllocCallPreserved _ sf_6›; simpa only [arm64_norm, wp_norm] using h)).trans
      (by have h := ‹AllocCallPreserved _ sf_7›; simpa only [arm64_norm, wp_norm] using h)
  apply SepWPp.of_sepWP (mid := (blkPl_374).base + 940#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.weaken_pre
    (by simp only [hst4, RustCliAllocBudget.pool_writeReg64, RustCliAllocBudget.pool_writeReg32,
      RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_setPState,
      RustCliAllocBudget.pool_advancePC, arm64_norm, wp_norm, *]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_3.readReg64 (Reg.gpr 0#5))
      (sf_5.readReg64 (Reg.gpr 0#5)) (sf_7.readReg64 (Reg.gpr 0#5))
      hoom12 hoom13 hoom14 hoom15
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, *]) (by simp only [arm64_norm, wp_norm, Reg.x0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x19, *]) (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x21, *]) (by simp only [arm64_norm, wp_norm, Reg.x23, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, *]) (by simp only [arm64_norm, wp_norm, Reg.x25, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, *]) (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]) (by simp only [arm64_norm, wp_norm, hacp15.2.1])
      (by simp only [arm64_norm, wp_norm, hacp15])
      (by simp only [arm64_norm, wp_norm, *]))

/-- Straight-line scatter of the 16 `Poly::zero()` headers (`+940 -> +1204`) in `[LibsignalPlacement]`,
    preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem polys_init_scatter_placed {A : CryptoVerification.RustHeap.RustAlloc}
    {ext : String → Option (State → State)}
    (s : State) (fsp out pbA polysPtr : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0#64) (hp1 : p1 ≠ 0#64) (hp2 : p2 ≠ 0#64) (hp3 : p3 ≠ 0#64)
    (hp4 : p4 ≠ 0#64) (hp5 : p5 ≠ 0#64) (hp6 : p6 ≠ 0#64) (hp7 : p7 ≠ 0#64)
    (hp8 : p8 ≠ 0#64) (hp9 : p9 ≠ 0#64) (hp10 : p10 ≠ 0#64) (hp11 : p11 ≠ 0#64)
    (hp12 : p12 ≠ 0#64) (hp13 : p13 ≠ 0#64) (hp14 : p14 ≠ 0#64) (hp15 : p15 ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 940#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = p15) (hx19 : s.readReg64 .x19 = p8)
    (hx20 : s.readReg64 .x20 = p0) (hx21 : s.readReg64 .x21 = p9)
    (hx23 : s.readReg64 .x23 = p10) (hx24 : s.readReg64 .x24 = p11)
    (hx25 : s.readReg64 .x25 = p12) (hx26 : s.readReg64 .x26 = p13)
    (hx27 : s.readReg64 .x27 = p14) (hx29 : s.readReg64 .x29 = fsp + 928#64) :
    SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      ((blkPl_374).base + 1204#64)
      s
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗
        Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          cells fsp 7 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          ((pbA + 32#64) ↦₆₄ polysPtr) ∗
          zeroPolySlotsAt A (fsp + 480#64) 16 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x22 = 0#64 ∧
        sm.readReg64 .x23 = fsp + 864#64 ∧
        sm.readReg64 .x24 = polysPtr ∧
        sm.readReg64 .x28 = 0#64 ∧
        sm.readReg64 .x29 = fsp + 928#64 ∧
        sm.trace = s.trace ∧
        AllocCallPreserved s sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  rw [show
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗ Frame) =
      (cells (fsp + 480#64) 48 ∗
       ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗
        A.live p12 2 2 ∗ memRegion p12 2 ∗ A.live p13 2 2 ∗ memRegion p13 2 ∗
        A.live p14 2 2 ∗ memRegion p14 2 ∗ A.live p15 2 2 ∗ memRegion p15 2 ∗ Frame)) by sep_ac_rfl]
  iterate 48 (apply sepWP_cells_succ; intro _)
  apply sepWP_cells_zero
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  by_vm_steps (
    wp_steps
    refine align_pre_vm ?_ ?_
    · have hc7 :
          (fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
            ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ⊢
            cells fsp 7 := by
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p7 (sepConj_mono_right ?_)
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p6 ?_
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p5 ?_
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p4 ?_
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p3 ?_
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
        rw [ProofLib.cells_succ]; refine Entails.sepExists_right p2 ?_
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; refine sepConj_mono_right ?_
        rw [ProofLib.cells_succ, ProofLib.cells_zero]
        simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp]
        exact Entails.sepExists_right p1 (Entails.refl _)
      dsimp only [zeroPolySlotsAt]
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
      have hz0 := zeroPolySlotAt_intro A (fsp + 480#64) p0 hp0
      have hz1 := zeroPolySlotAt_intro A (fsp + 504#64) p1 hp1
      have hz2 := zeroPolySlotAt_intro A (fsp + 528#64) p2 hp2
      have hz3 := zeroPolySlotAt_intro A (fsp + 552#64) p3 hp3
      have hz4 := zeroPolySlotAt_intro A (fsp + 576#64) p4 hp4
      have hz5 := zeroPolySlotAt_intro A (fsp + 600#64) p5 hp5
      have hz6 := zeroPolySlotAt_intro A (fsp + 624#64) p6 hp6
      have hz7 := zeroPolySlotAt_intro A (fsp + 648#64) p7 hp7
      have hz8 := zeroPolySlotAt_intro A (fsp + 672#64) p8 hp8
      have hz9 := zeroPolySlotAt_intro A (fsp + 696#64) p9 hp9
      have hz10 := zeroPolySlotAt_intro A (fsp + 720#64) p10 hp10
      have hz11 := zeroPolySlotAt_intro A (fsp + 744#64) p11 hp11
      have hz12 := zeroPolySlotAt_intro A (fsp + 768#64) p12 hp12
      have hz13 := zeroPolySlotAt_intro A (fsp + 792#64) p13 hp13
      have hz14 := zeroPolySlotAt_intro A (fsp + 816#64) p14 hp14
      have hz15 := zeroPolySlotAt_intro A (fsp + 840#64) p15 hp15
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7
      simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz8 hz9 hz10 hz11 hz12 hz13 hz14 hz15
      refine Entails.trans ?_
        (sepConj_mono hc7 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono hz0 (sepConj_mono hz1 (sepConj_mono hz2 (sepConj_mono hz3
          (sepConj_mono hz4 (sepConj_mono hz5 (sepConj_mono hz6 (sepConj_mono hz7
          (sepConj_mono hz8 (sepConj_mono hz9 (sepConj_mono hz10 (sepConj_mono hz11
          (sepConj_mono hz12 (sepConj_mono hz13 (sepConj_mono hz14
          (sepConj_mono_left hz15))))))))))))))))))))
      exact Entails.of_eq (by sep_ac_rfl)
    · wp_done
  )

/-- Combined 16-slot `Poly::zero()` initialization (`+556 -> +1204`) under
    `FitsEvents M lim st encoderFromPbPolysInitEvents` in `[LibsignalPlacement]`. -/
theorem polys_init_zero_headers_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)} {Q Qp : State → SepProp → Prop}
    (hshim : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustNoAllocShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
      (lsρ spqrRustAllocSym) (rustCliAllocBudgetSpec M A lim false))
    (st : M.σ) (hFit : FitsEvents M lim st encoderFromPbPolysInitEvents)
    (s0 s : State) (fsp out pbA polysPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_374).base + 556#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out) (hx1 : s.readReg64 .x1 = pbA)
    (hx29 : s.readReg64 .x29 = fsp + 928#64)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcont : ∀ sm,
      sm.pc = (blkPl_374).base + 1204#64 →
      sm.status = .Running → sm.sp = fsp →
      sm.readReg64 .x22 = 0#64 → sm.readReg64 .x23 = fsp + 864#64 →
      sm.readReg64 .x24 = polysPtr → sm.readReg64 .x28 = 0#64 →
      sm.readReg64 .x29 = fsp + 928#64 → sm.trace = s0.trace →
      AllocCallPreserved s0 sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) sm
        (cells fsp 7 ∗
          ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
          ((pbA + 32#64) ↦₆₄ polysPtr) ∗
          zeroPolySlotsAt A.repAlloc (fsp + 480#64) 16 ∗
          A.pool lim (M.stepEvents encoderFromPbPolysInitEvents st) sm ∗
          stackAt fsp allocHookStack ∗ Frame)
        Q Qp) :
    SepWPp ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (cells fsp 4 ∗ cells (fsp + 32#64) 5 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗
        cells (fsp + 480#64) 48 ∗ A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Qp := by
  have hFit' : FitsEvents M lim st
      (polysAlloc4Events ++ (polysAlloc4Events ++ (polysAlloc4Events ++ polysAlloc4Events))) := by
    rwa [← encoderFromPbPolysInitEvents_eq]
  rcases (peel_fits hFit') with ⟨hfit_a, hFit_bc⟩
  rcases (peel_fits hFit_bc) with ⟨hfit_b, hFit_cd⟩
  rcases (peel_fits hFit_cd) with ⟨hfit_c, hfit_d⟩
  have hst_all : M.stepEvents polysAlloc4Events
      (M.stepEvents polysAlloc4Events
        (M.stepEvents polysAlloc4Events (M.stepEvents polysAlloc4Events st))) =
      M.stepEvents encoderFromPbPolysInitEvents st := by
    simp only [encoderFromPbPolysInitEvents_eq, AllocCostModel.stepEvents_append]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (polys_alloc_0_3_placed hshim halloc st hfit_a s0 s fsp out pbA hfsp_align
      (cells fsp 4 ∗ ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗ Frame)
      hpc hrun hsp hx0 hx1 htrace hacp hvregs ?_)
  intro s1 p0 p1 p2 p3 hp0 hp1 hp2 hp3 hpc1 hrun1 hsp1 hx20_1 hx29_1 htr1 hacp1 hvregs1
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (polys_alloc_4_7_placed hshim halloc _ hfit_b s0 s1 fsp hfsp_align
      (((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗ Frame)
      hpc1 hrun1 hsp1 htr1 hacp1 hvregs1 ?_)
  intro s2 p4 p5 p6 p7 hp4 hp5 hp6 hp7 hpc2 hrun2 hsp2 hx20_2 hx29_2 htr2 hacp2 hvregs2
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (polys_alloc_8_11_placed hshim halloc _ hfit_c s0 s2 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗ Frame)
      hpc2 hrun2 hsp2 htr2 hacp2 hvregs2 ?_)
  intro s3 p8 p9 p10 p11 hp8 hp9 hp10 hp11 hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx23_3 hx24_3 hx29_3 htr3 hacp3 hvregs3
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (polys_alloc_12_15_placed hshim halloc _ hfit_d s0 s3 fsp hfsp_align
      ((fsp ↦₆₄ p7) ∗ ((fsp + 8#64) ↦₆₄ p6) ∗ ((fsp + 16#64) ↦₆₄ p5) ∗ ((fsp + 24#64) ↦₆₄ p4) ∗
        ((fsp + 32#64) ↦₆₄ p3) ∗ ((fsp + 40#64) ↦₆₄ p2) ∗ ((fsp + 48#64) ↦₆₄ p1) ∗
        ((fsp + 56#64) ↦₆₄ out) ∗ ((fsp + 64#64) ↦₆₄ pbA) ∗
        ((pbA + 32#64) ↦₆₄ polysPtr) ∗ cells (fsp + 480#64) 48 ∗
        A.live p0 2 2 ∗ memRegion p0 2 ∗ A.live p1 2 2 ∗ memRegion p1 2 ∗
        A.live p2 2 2 ∗ memRegion p2 2 ∗ A.live p3 2 2 ∗ memRegion p3 2 ∗
        A.live p4 2 2 ∗ memRegion p4 2 ∗ A.live p5 2 2 ∗ memRegion p5 2 ∗
        A.live p6 2 2 ∗ memRegion p6 2 ∗ A.live p7 2 2 ∗ memRegion p7 2 ∗
        A.live p8 2 2 ∗ memRegion p8 2 ∗ A.live p9 2 2 ∗ memRegion p9 2 ∗
        A.live p10 2 2 ∗ memRegion p10 2 ∗ A.live p11 2 2 ∗ memRegion p11 2 ∗ Frame)
      hpc3 hrun3 hsp3 htr3 hacp3 hvregs3 ?_)
  intro s4 p12 p13 p14 p15 hp12 hp13 hp14 hp15 hpc4 hrun4 hsp4
    hx0_4 hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 htr4 hacp4 hvregs4
  rw [hst_all]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (seq_vm_wpp
      (polys_init_scatter_placed (A := A.repAlloc) (ext := ext) s4 fsp out pbA polysPtr
        p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
        hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
        hfsp_align (A.pool lim (M.stepEvents encoderFromPbPolysInitEvents st) s4 ∗
          stackAt fsp allocHookStack ∗ Frame)
        hpc4 hrun4 hsp4 hx0_4
        (by rw [hx19_4, hx19_3])
        (by rw [hx20_4, hx20_3, hx20_2, hx20_1])
        (by rw [hx21_4, hx21_3])
        (by rw [hx23_4, hx23_3])
        (by rw [hx24_4, hx24_3])
        hx25_4 hx26_4 hx27_4
        (by rw [hx29_4, hx29_3, hx29_2, hx29_1, hx29]))
      ?_)
  intro s5 hpc5 hrun5 hvm5 ⟨hsp5, hx22_5, hx23_5, hx24_5, hx28_5, hx29_5, htr5, hacp45, hvregs5⟩
  rw [← A.pool_of_vmPreserved hvm5]
  exact hcont s5 hpc5 hrun5 hsp5 hx22_5 hx23_5 hx24_5 hx28_5 hx29_5
    (by rw [htr5, htr4]) (hacp4.trans hacp45) (by rw [hvregs5, hvregs4])

/-- `.polys` inner loop (`+1308 -> +1356`) in `[LibsignalPlacement]`, preserving `VmPreserved`
    and `AllocCallPreserved`. -/
theorem polys_inner_loop_placed {ext : String → Option (State → State)} :
    ∀ (n : Nat) (bs : List (BitVec 8)) (k totalGF16 : Nat) (s : State)
      (fsp bsPtr outPtr v_len : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp),
      bs.length = 2 * (n + 1) →
      k + (n + 1) = totalGF16 →
      2 * totalGF16 < 2 ^ 63 →
      s.pc = (blkPl_374).base + 1308#64 →
      s.status = .Running →
      s.sp = fsp →
      s.readReg64 .x0 = outPtr →
      s.readReg64 .x19 = bsPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) →
      s.readReg64 .x26 = BitVec.ofNat 64 (2 * k) →
      s.readReg64 .x27 = BitVec.ofNat 64 (k + 1) →
      s.readReg64 .x29 = fsp + 928#64 →
      SepWP ((blkPC_374).rebase (blkPl_374).base (Rust.withPanics ext))
        ((blkPl_374).base + 1356#64)
        s
        (((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
          ((fsp + 912#64) ↦₆₄ v_len) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * k)) bs.length ∗
          Frame)
        (fun sm Pm =>
          VmPreserved s sm ∧
          (Pm ⊢ ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
            ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (k + n + 1)) ∗
            ((bsPtr + BitVec.ofNat 64 (2 * k)) ↦ₛ bs) ∗
            arrayAt gf16At 2 (outPtr + BitVec.ofNat 64 (2 * k)) (bytesToGF16ListTotal bs) ∗
            Frame) ∧
          sm.sp = fsp ∧
          sm.readReg64 .x0 = outPtr ∧
          sm.readReg64 .x19 = bsPtr ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = fsp + 928#64 ∧
          sm.trace = s.trace ∧
          AllocCallPreserved s sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s) := by
  intro n
  induction n with
  | zero =>
    intro bs k totalGF16 s fsp bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx0 hx19 hx21 hx26 hx27 hx29
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · have htot2 : 2 * k + 2 = 2 * totalGF16 := by omega
      have hlt1 : 2 * k < 2 * totalGF16 := by omega
      have hlt2 : 2 * k + 1 < 2 * totalGF16 := by omega
      have hk_lt : k < totalGF16 := by omega
      have hmax64 : 2 * totalGF16 < 2 ^ 64 := by omega
      have hgf64 : totalGF16 < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt2 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalGF16) = true :=
        bne_of_lt hk_lt hgf64
      have h_bne' : (BitVec.ofNat 64 totalGF16 != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hgf64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalGF16) = false :=
        beq_false_of_lt hk_lt hgf64
      have h_beq' : (BitVec.ofNat 64 totalGF16 == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hgf64
      have h_end_eq : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * totalGF16) :=
        congrArg (BitVec.ofNat 64) htot2
      have htot1 : k + 1 = totalGF16 := by omega
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 []]
      dsimp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
      rw [ProofLib.memRegion_two (outPtr + BitVec.ofNat 64 (2 * k))]
      simp only [ProofLib.pointsToBytes_nil, sepConj_emp, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      by_vm_steps (
        wp_steps
        refine align_pre_vm ?_ ?_
        · dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new]
          simp only [ProofLib.pointsToBytes_nil, Nat.add_zero, htot1, sepConj_emp,
            rev16_pair_eq_u16FromBeBytes]
          exact Entails.of_eq (by sep_ac_rfl)
        · wp_done
      )
    · simp at hlen
  | succ n ih =>
    intro bs k totalGF16 s fsp bsPtr outPtr v_len hfsp_align Frame
      hlen htot hmax hpc hrun hsp hx0 hx19 hx21 hx26 hx27 hx29
    rcases bs with _ | ⟨b0, _ | ⟨b1, bs'⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : bs'.length = 2 * (n + 1) := by simp at hlen; omega
      have htot' : (k + 1) + (n + 1) = totalGF16 := by omega
      have hlt1 : 2 * k < 2 * totalGF16 := by omega
      have hlt2 : 2 * k + 1 < 2 * totalGF16 := by omega
      have hlt3 : 2 * k + 2 < 2 * totalGF16 := by omega
      have hk_lt : k < totalGF16 := by omega
      have hmax64 : 2 * totalGF16 < 2 ^ 64 := by omega
      have hgf64 : totalGF16 < 2 ^ 64 := by omega
      have h_ule1 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k)) = false :=
        ule_false_of_lt hlt1 hmax64
      have h_ult1 : BitVec.ult (BitVec.ofNat 64 (2 * k)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt1 hmax64
      have h_ule2 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 1)) = false :=
        ule_false_of_lt hlt2 hmax64
      have h_ult2 : BitVec.ult (BitVec.ofNat 64 (2 * k + 1)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt2 hmax64
      have h_ule3 : BitVec.ule (BitVec.ofNat 64 (2 * totalGF16)) (BitVec.ofNat 64 (2 * k + 2)) = false :=
        ule_false_of_lt hlt3 hmax64
      have h_ult3 : BitVec.ult (BitVec.ofNat 64 (2 * k + 2)) (BitVec.ofNat 64 (2 * totalGF16)) = true :=
        ult_of_lt hlt3 hmax64
      have h_bne : (BitVec.ofNat 64 k != BitVec.ofNat 64 totalGF16) = true :=
        bne_of_lt hk_lt hgf64
      have h_bne' : (BitVec.ofNat 64 totalGF16 != BitVec.ofNat 64 k) = true :=
        bne_of_gt hk_lt hgf64
      have h_beq : (BitVec.ofNat 64 k == BitVec.ofNat 64 totalGF16) = false :=
        beq_false_of_lt hk_lt hgf64
      have h_beq' : (BitVec.ofNat 64 totalGF16 == BitVec.ofNat 64 k) = false :=
        beq_false_of_gt hk_lt hgf64
      have hbs_len_eq : (b0 :: b1 :: bs').length = 2 * ((n + 1) + 1) := by
        simp [hlen']; omega
      have hbs_addr : bsPtr + BitVec.ofNat 64 (2 * k + 2) = bsPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
        congr 2
      rw [pointsToBytes_pair_cons (bsPtr + BitVec.ofNat 64 (2 * k)) b0 b1 bs',
          bv_add_lit_add_lit, hbs_addr, hbs_len_eq,
          memRegion_two_cons outPtr k (n + 1) (by omega),
          ← hlen']
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro d16
      refine seq_vm_clean
        (mid := (blkPl_374).base + 1308#64)
        (P_mid :=
          ((fsp + 896#64) ↦₆₄ BitVec.ofNat 64 totalGF16) ∗
          ((fsp + 912#64) ↦₆₄ BitVec.ofNat 64 (k + 1)) ∗
          ((bsPtr + BitVec.ofNat 64 (2 * (k + 1))) ↦ₛ bs') ∗
          memRegion (outPtr + BitVec.ofNat 64 (2 * (k + 1))) bs'.length ∗
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame))
        (Q := fun sm =>
          sm.sp = fsp ∧
          sm.readReg64 .x0 = outPtr ∧
          sm.readReg64 .x19 = bsPtr ∧
          sm.readReg64 .x20 = s.readReg64 .x20 ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (2 * totalGF16) ∧
          sm.readReg64 .x22 = s.readReg64 .x22 ∧
          sm.readReg64 .x23 = s.readReg64 .x23 ∧
          sm.readReg64 .x24 = s.readReg64 .x24 ∧
          sm.readReg64 .x26 = BitVec.ofNat 64 (2 * (k + 1)) ∧
          sm.readReg64 .x27 = BitVec.ofNat 64 ((k + 1) + 1) ∧
          sm.readReg64 .x28 = s.readReg64 .x28 ∧
          sm.readReg64 .x29 = fsp + 928#64 ∧
          sm.trace = s.trace ∧
          AllocCallPreserved s sm ∧
          calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · by_vm_steps (
          wp_steps
          refine align_pre_vm ?_ ?_
          · simp only [rev16_pair_eq_u16FromBeBytes]
            exact Entails.of_eq (by sep_ac_rfl)
          · have hk2 : BitVec.ofNat 64 (2 * k + 2) = BitVec.ofNat 64 (2 * (k + 1)) := by
              congr 1
            wp_done
        )
      · intro sm hpcm hrunm hvm1 ⟨hspm, hx0m, hx19m, hx20m, hx21m, hx22m, hx23m, hx24m,
          hx26m, hx27m, hx28m, hx29m, htrm, hacpm, hvregsm⟩
        have hstep := ih bs' (k + 1) totalGF16 sm fsp bsPtr outPtr (BitVec.ofNat 64 (k + 1))
          hfsp_align
          (((bsPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ (b1 ++ b0)) ∗
            ((outPtr + BitVec.ofNat 64 (2 * k)) ↦₁₆ u16FromBeBytes b0 b1) ∗
            Frame)
          hlen' htot' hmax hpcm hrunm hspm hx0m hx19m hx21m hx26m hx27m hx29m
        refine sepWP_map_post hstep ?_
        intro sf Pf ⟨hvm2, hPf, hspf, hx0f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f,
          hx28f, hx29f, htrf, hacpf, hvregsf⟩
        refine ⟨hvm1.trans hvm2, Entails.trans hPf ?_, hspf, hx0f, hx19f, by rw [hx20f, hx20m],
          hx21f, by rw [hx22f, hx22m], by rw [hx23f, hx23m], by rw [hx24f, hx24m],
          by rw [hx28f, hx28m], hx29f, by rw [htrf, htrm], hacpm.trans hacpf,
          by rw [hvregsf, hvregsm]⟩
        have hk_assoc : (k + 1) + n + 1 = k + (n + 1) + 1 := by omega
        have hout_addr : outPtr + BitVec.ofNat 64 (2 * k) + 2#64 =
            outPtr + BitVec.ofNat 64 (2 * (k + 1)) := by
          rw [BitVec.add_assoc, ofNat_add_two]
        dsimp only [bytesToGF16ListTotal, arrayAt, gf16At, GF16.new, BitVec.ofNat_eq_ofNat]
        rw [hk_assoc, hout_addr]
        exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.PolysLoopPlacedBudget
