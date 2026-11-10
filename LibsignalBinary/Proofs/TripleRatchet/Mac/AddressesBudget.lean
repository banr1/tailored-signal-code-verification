/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded Relocatable `<SignalMessage>::serialize_addresses`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`serializeAddressesSpec` and
`serializeAddressesSpecX`) for `<SignalMessage>::serialize_addresses`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded withLsCodeLoaded lsmpl lsρ
   blkPC_61 blkPl_61 blkLib_eq_61)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (UuidParser kindByte noneCap protocolAddressAt serializeAddresses serviceIdParse uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (ParseSidCellsGhost extHookStack kindByte_beq_two kindByte_bne_two
   kindByte_zext32_beq_two kindByte_zext32_bne_two
   kindByte_zext64_beq_two kindByte_zext64_bne_two
   lsMacRustAllocSym lsMacRustNoAllocShimSym
   mac_ls_externAt?_of_mem mac_ls_hook_ok_of_mem
   memRegion_16_ret_split memRegion_17_eq memRegion_24_ret_split memRegion_36_addr_split
   noAllocShimSpec optSerializeAddressesAt
   optSerializeAddressesAt_some_36_eq parseSidCellsResultAt parseSidCellsSpecAt
   parseSidCodeSpec parseSidCodeStackSpec parseSidFrameStack parseSidResultAt_eq_cells
   parseSidSpec parseSidStack pointsTo_17_entails_memRegion protocolAddressAt_expose
   sepWPp_seq_lscl shimSpecWithStack subroutine_ok_withStack_of_subroutine_ok
   uuidTryParseStack uuidWord0 uuidWord1 withStack)
open CryptoVerification.LibsignalTripleRatchet.AddressesStateSimp
  (readReg_setMem_setPC_pre readReg_setPC_pre readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk VmPreserved
   rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack
   rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas
  (subroutine_ok_allocNoOom_externWithStack_of_hookSat
   subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
  (parseSidCodeBudgetSpec parseSidCodeStackBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (SerializeAddressesEnv serializeAddressesEvents serializeAddressesSpec
   serializeAddressesSpecAt serializeAddressesSpecX fitsEnv_serializeAddresses_iff)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewPureBudget
  (noAllocShimBudgetSpec new_shim_placed_ok_of_rustAllocShimVm)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm]
  kindByte_beq_two kindByte_zext32_beq_two kindByte_zext64_beq_two
  kindByte_bne_two kindByte_zext32_bne_two kindByte_zext64_bne_two

/-! ## Stack decomposition and `VmPreserved` callee wrappers -/

private def serializeAddressesFrameRest (sp : BitVec 64) : SepProp :=
  memRegion (sp - 96#64) 12 ∗ memRegion (sp - 67#64) 3

private theorem stackAt_serializeAddresses_at {callStack : Nat}
    (hbound : callStack + 128 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (callStack + 128) =
      stackAt (sp - 128#64) callStack ∗
      serializeAddressesFrameRest sp ∗
      (∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 128#64) ↦₆₄ q0) ∗ ((sp - 120#64) ↦₆₄ q1) ∗
        ((sp - 112#64) ↦₆₄ q2) ∗ ((sp - 104#64) ↦₆₄ q3)) ∗
      (∃∗ b0 : BitVec 8, ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 84#64) ↦₈ b0) ∗ ((sp - 83#64) ↦₆₄ w0) ∗ ((sp - 75#64) ↦₆₄ w1)) ∗
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
       ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ s0) ∗ ((sp - 56#64) ↦₆₄ s1) ∗
        ((sp - 48#64) ↦₆₄ s2) ∗ ((sp - 40#64) ↦₆₄ s3) ∗
        ((sp - 32#64) ↦₆₄ s4) ∗ ((sp - 24#64) ↦₆₄ s5) ∗
        ((sp - 16#64) ↦₆₄ s6) ∗ ((sp - 8#64) ↦₆₄ s7)) := by
  unfold serializeAddressesFrameRest
  have htop : stackAt sp (callStack + 128) =
      stackAt (sp - 128#64) callStack ∗ memRegion (sp - 128#64) 128 := by
    simp only [stackAt]
    rw [memRegion_split _ callStack 128 hbound]
    have e1 : sp - BitVec.ofNat 64 (callStack + 128) =
        sp - 128#64 - BitVec.ofNat 64 callStack := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
    have e2 : sp - 128#64 - BitVec.ofNat 64 callStack + BitVec.ofNat 64 callStack =
        sp - 128#64 := BitVec.sub_add_cancel _ _
    rw [e1, e2]
  rw [htop]
  have hm128 : memRegion (sp - 128#64) 128 =
      memRegion (sp - 128#64) (8 * 4) ∗
      memRegion (sp - 96#64) 12 ∗
      memRegion (sp - 84#64) 17 ∗
      memRegion (sp - 67#64) 3 ∗
      memRegion (sp - 64#64) (8 * 8) := by
    rw [show (128 : Nat) = 32 + (12 + (17 + (3 + 64))) by decide,
      memRegion_split (sp - 128#64) 32 (12 + (17 + (3 + 64))) (by decide),
      memRegion_split (sp - 128#64 + 32#64) 12 (17 + (3 + 64)) (by decide),
      memRegion_split (sp - 128#64 + 32#64 + 12#64) 17 (3 + 64) (by decide),
      memRegion_split (sp - 128#64 + 32#64 + 12#64 + 17#64) 3 64 (by decide)]
    have a1 : sp - 128#64 + 32#64 = sp - 96#64 := by bv_arith
    have a2 : sp - 96#64 + 12#64 = sp - 84#64 := by bv_arith
    have a3 : sp - 84#64 + 17#64 = sp - 67#64 := by bv_arith
    have a4 : sp - 67#64 + 3#64 = sp - 64#64 := by bv_arith
    rw [a1, a2, a3, a4]
  rw [hm128, memRegion_cells (sp - 128#64) 4 (by decide),
    memRegion_cells (sp - 64#64) 8 (by decide),
    memRegion_17_eq (sp - 84#64)]
  have hc4 : cells (sp - 128#64) 4 =
      ∃∗ q0 : BitVec 64, ∃∗ q1 : BitVec 64, ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64,
        ((sp - 128#64) ↦₆₄ q0) ∗ ((sp - 120#64) ↦₆₄ q1) ∗
        ((sp - 112#64) ↦₆₄ q2) ∗ ((sp - 104#64) ↦₆₄ q3) := by
    cells_unfold
  have hc8 : cells (sp - 64#64) 8 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64, ∃∗ s3 : BitVec 64,
      ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64, ∃∗ s6 : BitVec 64, ∃∗ s7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ s0) ∗ ((sp - 56#64) ↦₆₄ s1) ∗
        ((sp - 48#64) ↦₆₄ s2) ∗ ((sp - 40#64) ↦₆₄ s3) ∗
        ((sp - 32#64) ↦₆₄ s4) ∗ ((sp - 24#64) ↦₆₄ s5) ∗
        ((sp - 16#64) ↦₆₄ s6) ∗ ((sp - 8#64) ↦₆₄ s7) := by
    cells_unfold
  have ha1 : sp - 84#64 + 1#64 = sp - 83#64 := by bv_arith
  have ha2 : sp - 84#64 + 9#64 = sp - 75#64 := by bv_arith
  rw [hc4, hc8, ha1, ha2]
  sep_ac_rfl

private theorem stackAt_allocHookStack_eq_parseSid (sp : BitVec 64) :
    stackAt sp allocHookStack =
      stackAt sp parseSidStack ∗ memRegion (sp - 4096#64) 3824 := by
  show stackAt sp (parseSidStack + 3824) = _
  rw [ProofLib.stackAt_split_bottom sp parseSidStack 3824 (by decide)]
  exact sepConj_comm _ _

private theorem stackAt_parseSid_add_extHook (sp : BitVec 64) :
    stackAt sp (parseSidStack + extHookStack) =
      stackAt (sp - 80#64) extHookStack ∗ stackAt sp parseSidFrameStack ∗
        memRegion (sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack := by
  have h1 : stackAt sp (parseSidStack + extHookStack) =
      memRegion (sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack ∗
        stackAt sp (parseSidFrameStack + extHookStack) := by
    rw [show parseSidStack + extHookStack = (parseSidFrameStack + extHookStack) + uuidTryParseStack
      by decide]
    exact ProofLib.stackAt_split_bottom sp (parseSidFrameStack + extHookStack) uuidTryParseStack
      (by decide)
  have h2 : stackAt sp (parseSidFrameStack + extHookStack) =
      stackAt (sp - 80#64) extHookStack ∗ stackAt sp parseSidFrameStack := by
    simp only [stackAt, parseSidFrameStack]
    rw [show (0x50 + extHookStack : Nat) = extHookStack + 80 by omega,
      memRegion_split _ extHookStack 80 (by decide)]
    have e1 : sp - BitVec.ofNat 64 (extHookStack + 80) =
        sp - 80#64 - BitVec.ofNat 64 extHookStack := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
    have e2 : sp - 80#64 - BitVec.ofNat 64 extHookStack + BitVec.ofNat 64 extHookStack =
        sp - 80#64 := BitVec.sub_add_cancel _ _
    rw [e1, e2]
  rw [h1, h2]
  sep_ac_rfl

/-- `VmPreserved`-strengthened counterpart of `shimSpecWithStack`. -/
def shimBudgetSpecWithStack (hookStack : Nat) : Spec Unit :=
  withVmPreserved (shimSpecWithStack hookStack)

/-- `VmPreserved`-strengthened counterpart of `parseSidCellsSpecAt`. -/
def parseSidCellsBudgetSpecAt (parse : UuidParser) (callStack : Nat) : Spec ParseSidCellsGhost :=
  withVmPreserved (parseSidCellsSpecAt parse callStack)

theorem shimBudgetWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimBudgetSpec) :
    subroutine_ok prog addr (shimBudgetSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimBudgetSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimBudgetSpec, shimBudgetSpecWithStack, withVmPreserved,
      noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  refine h'.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex | hoom)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, noAllocShimBudgetSpec, shimBudgetSpecWithStack, withVmPreserved,
      noAllocShimSpec, shimSpecWithStack] at hpost ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem shimBudgetSpecWithStack_widen {P : Program} {addr : BitVec 64}
    {s1 extra : Nat} (hbound : s1 + extra ≤ 2 ^ 64)
    (h : subroutine_ok P addr (shimBudgetSpecWithStack s1)) :
    subroutine_ok P addr (shimBudgetSpecWithStack (extra + s1)) := by
  have hsplit : ∀ sp : BitVec 64,
      stackAt sp (extra + s1) =
        stackAt sp s1 ∗ memRegion (sp - BitVec.ofNat 64 (extra + s1)) extra := by
    intro sp
    rw [Nat.add_comm extra s1, ProofLib.stackAt_split_bottom sp s1 extra hbound, sepConj_comm]
  refine subroutine_ok_outcome_intro fun ⟨⟩ R s0 hpc hrun hpre hal => ?_
  let F := memRegion (s0.sp - BitVec.ofNat 64 (extra + s1)) extra
  have hpre' : s0.mem ⊨ (shimBudgetSpecWithStack s1).pre () s0 ∗ (F ∗ R) := by
    simp only [shimBudgetSpecWithStack, withVmPreserved, shimSpecWithStack, hsplit, F] at hpre ⊢
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hpre
    sep_ac_rfl
  refine h.mono_outcome () (F ∗ R) s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hs, hp⟩ | ⟨c, hs, he⟩ | ⟨hs, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [shimBudgetSpecWithStack, withVmPreserved, shimSpecWithStack, hsplit, F] at hpost ⊢
    refine Eq.mp (congrArg (fun Q => sf.mem ⊨ Q) ?_) hpost
    sep_ac_rfl
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem parseSidCellsBudget_of_parseSidCode [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    {parse : UuidParser}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse))) :
    subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCellsBudgetSpecAt parse allocHookStack)) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out, b0, w0, w1⟩ R s0 hpc hrun hpre hal => ?_
  let F := memRegion (s0.sp - 4096#64) 3824
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)).pre (p, bs, out) s0 ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, parseSidCodeBudgetSpec,
      withVmPreserved, F] at hpre ⊢
    simp only [parseSidCellsSpecAt, parseSidCodeSpec, parseSidSpec,
      stackAt_allocHookStack_eq_parseSid] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          (p ↦ₛ bs) ∗ stackAt s0.sp parseSidStack ∗ memRegion (s0.sp - 4096#64) 3824 ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hpre
      sep_ac_rfl
    have hm' := Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion out b0 w0 w1)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm'
    sep_ac_rfl
  refine h.mono_outcome (p, bs, out) (F ∗ R) s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hs, hp⟩ | ⟨c, hs, he⟩ | ⟨hs, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, parseSidCodeBudgetSpec,
      withVmPreserved, F] at hpost ⊢
    simp only [parseSidCodeSpec, parseSidSpec, parseSidCellsSpecAt,
      parseSidResultAt_eq_cells, stackAt_allocHookStack_eq_parseSid] at hpost ⊢
    refine Eq.mp (congrArg (fun Q => sf.mem ⊨ Q) ?_) hpost
    sep_ac_rfl
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem parseSidCellsBudget_of_parseSidStack [LibsignalPlacement] {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack))) :
    subroutine_ok P addr
      (withLsCodeLoaded lsmpl
        (parseSidCellsBudgetSpecAt uuidTryParse (parseSidStack + extHookStack))) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out, b0, w0, w1⟩ R s0 hpc hrun hpre hal => ?_
  let F := memRegion (s0.sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack
  have hpre' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack)).pre (p, bs, out) s0 ∗
        (F ∗ R) := by
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, parseSidCodeStackBudgetSpec,
      withVmPreserved, F] at hpre ⊢
    simp only [parseSidCellsSpecAt, parseSidCodeStackSpec, parseSidSpec,
      stackAt_parseSid_add_extHook] at hpre ⊢
    have hm : s0.mem ⊨ ((out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1)) ∗
        (⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
          ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = bs.length ∧ s0.readReg64 .x8 = out⌝ ∗
          (p ↦ₛ bs) ∗ stackAt (s0.sp - 80#64) extHookStack ∗ stackAt s0.sp parseSidFrameStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 (parseSidStack + extHookStack)) uuidTryParseStack ∗ R) := by
      refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hpre
      sep_ac_rfl
    have hm' := Satisfies.mono (sepConj_mono_left (pointsTo_17_entails_memRegion out b0 w0 w1)) hm
    refine Eq.mp (congrArg (fun Q => s0.mem ⊨ Q) ?_) hm'
    sep_ac_rfl
  refine h.mono_outcome (p, bs, out) (F ∗ R) s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hs, hp⟩ | ⟨c, hs, he⟩ | ⟨hs, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, parseSidCodeStackBudgetSpec,
      withVmPreserved, F] at hpost ⊢
    simp only [parseSidCodeStackSpec, parseSidSpec, parseSidCellsSpecAt,
      parseSidResultAt_eq_cells, stackAt_parseSid_add_extHook] at hpost ⊢
    refine Eq.mp (congrArg (fun Q => sf.mem ⊨ Q) ?_) hpost
    sep_ac_rfl
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem parseSidCellsBudget_placed_ok_at_state [LibsignalPlacement] {prog : Program}
    {parse : UuidParser} {callStack : Nat} {addr : BitVec 64} {s : State}
    (hparse : subroutine_ok prog addr
      (withLsCodeLoaded lsmpl (parseSidCellsBudgetSpecAt parse callStack)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok prog addr
      { pre := fun ((p, bs, out, b0, w0, w1) : ParseSidCellsGhost) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = bs.length ∧ s'.readReg64 .x8 = out⌝ ∗
            (p ↦ₛ bs) ∗ (out ↦₈ b0) ∗ ((out + 1#64) ↦₆₄ w0) ∗ ((out + 9#64) ↦₆₄ w1) ∗
            stackAt s'.sp callStack
        post := fun ((p, bs, out, _, _, _) : ParseSidCellsGhost) s0 sf =>
          ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
            (p ↦ₛ bs) ∗ parseSidCellsResultAt out (serviceIdParse parse bs) ∗
            stackAt s0.sp callStack } := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out, b0, w0, w1⟩ R s0 hpc hrun hm hsp => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  have hm' : s0.mem ⊨
      (withLsCodeLoaded lsmpl (parseSidCellsBudgetSpecAt parse callStack)).pre
        (p, bs, out, b0, w0, w1) s0 ∗ R := by
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, withVmPreserved, parseSidCellsSpecAt]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hmem ▸ hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hrest, hspatial⟩
  refine hparse.mono_outcome (p, bs, out, b0, w0, w1) R s0 hpc hrun hm' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hs, hp⟩ | ⟨c, hs, he⟩ | ⟨hs, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, parseSidCellsBudgetSpecAt, withVmPreserved,
      parseSidCellsSpecAt] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm0, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hrest_post⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvm0, htr⟩, hrest_post⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem shimBudget_unfold {prog : Program} {callStack : Nat} {addr : BitVec 64}
    (hshim : subroutine_ok prog addr (shimBudgetSpecWithStack callStack)) :
    subroutine_ok prog addr
      { pre := fun (_ : Unit) s' => stackAt s'.sp callStack
        post := fun _ s0 sf =>
          ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗ stackAt s0.sp callStack } := by
  refine subroutine_ok_outcome_intro fun ⟨⟩ R s0 hpc hrun hm hsp => ?_
  have hm' : s0.mem ⊨ (shimBudgetSpecWithStack callStack).pre () s0 ∗ R := by
    simpa only [shimBudgetSpecWithStack, withVmPreserved, shimSpecWithStack] using hm
  refine hshim.mono_outcome () R s0 hpc hrun hm' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hs, hp⟩ | ⟨c, hs, he⟩ | ⟨hs, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [shimBudgetSpecWithStack, withVmPreserved, shimSpecWithStack] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm0, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hrest_post⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hvm0, htr⟩, hrest_post⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## Relocatable `[LibsignalPlacement]` budget contracts -/

/-- Relocatable `[LibsignalPlacement]` budget proof of `<SignalMessage>::serialize_addresses`
(Block `61`) from `parseSid`, `shim`, and `allocNoOom` contracts at `callStack`. -/
theorem serialize_addresses_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {parse : UuidParser}
    {H : String → Option (State → State)} {callStack : Nat}
    (hbound : callStack + 128 ≤ 2 ^ 64 := by decide)
    (hparse_in : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCellsBudgetSpecAt parse callStack)))
    (hshim_in : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsρ lsMacRustNoAllocShimSym)
      (shimBudgetSpecWithStack callStack))
    (halloc : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsρ lsMacRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false callStack)) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpecAt M A lim parse callStack)) := by
  unfold withLsCodeLoaded
  simp only [serializeAddressesSpecAt, DefsBudget.serializeAddressesSpecWithStack,
    protocolAddressAt_expose, stackAt_serializeAddresses_at hbound,
    memRegion_24_ret_split, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x_st s0
  rcases x_st with ⟨x, st⟩
  have hfit_env : FitsEnv M lim st (SerializeAddressesEnv parse x) := by assumption
  have hfit_evs : FitsEvents M lim st (serializeAddressesEvents parse x) :=
    (fitsEnv_serializeAddresses_iff parse x).mp hfit_env
  obtain ⟨ret, senderA, sender, recipientA, recipient⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hlen_s : (BitVec.ofNat 64 sender.name.bytes.length).toNat = sender.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen_r : (BitVec.ofNat 64 recipient.name.bytes.length).toNat = recipient.name.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_seq_lscl (mid := lsmpl.base 206) hcl0
  wp_steps_sync_pool (lsmpl.base 206)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  have hparse1 := parseSidCellsBudget_placed_ok_at_state hparse_in hcl1
  apply sepWPp_seq_lscl (mid := (blkPl_61).base + 52#64) hcl1
  wp_call hparse1 (sender.name.ptr, sender.name.bytes, s0.sp - 84#64, v_stk_8, v_stk_9, v_stk_10)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  refine ProofLib.SepWPp.transport_budgetPool (by assumption) (hnext := ?_)
  have ha83 : s0.sp - 84#64 + 1#64 = s0.sp - 83#64 := by bv_arith
  have ha75 : s0.sp - 84#64 + 9#64 = s0.sp - 75#64 := by bv_arith
  cases hs : serviceIdParse parse sender.name.bytes with
  | none =>
    have hevs : serializeAddressesEvents parse ⟨ret, senderA, sender, recipientA, recipient⟩ = [] := by
      simp [serializeAddressesEvents, serializeAddresses, hs]
    rw [hevs, M.stepEvents_nil]
    simp only [parseSidCellsResultAt, serializeAddresses, hs, Option.bind_eq_bind, Option.bind,
      optSerializeAddressesAt, noneCap, ha83, ha75, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
    wp_done
  | some sval =>
    rcases sval with ⟨sPni, sUuid⟩
    simp only [parseSidCellsResultAt, ha83, ha75, sepConj_assoc]
    apply sepWPp_seq_lscl (mid := lsmpl.base 206) hcl2
    wp_steps_sync_pool (lsmpl.base 206)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl3
    have hparse2 := parseSidCellsBudget_placed_ok_at_state hparse_in hcl3
    apply sepWPp_seq_lscl (mid := (blkPl_61).base + 84#64) hcl3
    wp_call hparse2 (recipient.name.ptr, recipient.name.bytes, s0.sp - 84#64,
      kindByte sPni, uuidWord0 sUuid, uuidWord1 sUuid)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcl4
    refine ProofLib.SepWPp.transport_budgetPool (by assumption) (hnext := ?_)
    cases hr : serviceIdParse parse recipient.name.bytes with
    | none =>
      have hevs : serializeAddressesEvents parse ⟨ret, senderA, sender, recipientA, recipient⟩ = [] := by
        simp [serializeAddressesEvents, serializeAddresses, hs, hr]
      rw [hevs, M.stepEvents_nil]
      simp only [parseSidCellsResultAt, serializeAddresses, hs, hr, Option.bind_eq_bind,
        Option.bind, optSerializeAddressesAt, noneCap, ha83, ha75, sepExists_sepConj_left,
        sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      wp_done
    | some rval =>
      rcases rval with ⟨rPni, rUuid⟩
      have hevs : serializeAddressesEvents parse ⟨ret, senderA, sender, recipientA, recipient⟩ =
          rustAllocEvents 36 1 := by
        simp [serializeAddressesEvents, serializeAddresses, hs, hr]
      rw [hevs] at hfit_evs ⊢
      simp only [parseSidCellsResultAt, ha83, ha75, sepConj_assoc]
      have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      have hlay : RustLayoutOk 36 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
      have ⟨⟨hsz36, _, hsum36⟩, hal36⟩ := hlay
      obtain ⟨⟨_hwma, henf, hphys, hva⟩, -⟩ := hfit_evs
      apply SepWPp.of_sepWP (mid := lsρ lsMacRustNoAllocShimSym)
      wp_steps_sync_pool (lsρ lsMacRustNoAllocShimSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hshim1 := shimBudget_unfold hshim_in
      apply SepWPp.of_sepWP (mid := lsρ lsMacRustAllocSym)
      wp_call hshim1 ()
      refine ProofLib.SepWP.transport_budgetPool (by assumption) (hnext := ?_)
      wp_steps_sync_pool (lsρ lsMacRustAllocSym)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      apply SepWPp.of_sepWP (mid := (blkPl_61).base + 152#64)
      wp_call halloc (36, 1, st)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hsp_sf : sf_2.sp = s0.sp - 128#64 := by simp only [wp_norm, arm64_norm, *]
      simp only [wp_norm, arm64_norm, hsp_sf]
      try
        refine SepWPp.pure_elim fun ⟨_htr4, _hne0, _hal⟩ => ?_
      have hoom_ne : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by
        try simp only [wp_norm, arm64_norm] at *
        assumption
      have hoom_z : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom_ne
      have hoom_beq : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hoom_ne
      try simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      rw [memRegion_36_addr_split (sf_3.readReg64 (Reg.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun w1 =>
        SepWPp.exists_elim fun w9 => SepWPp.exists_elim fun b17 =>
        SepWPp.exists_elim fun b18 => SepWPp.exists_elim fun w19 =>
        SepWPp.exists_elim fun w27 => SepWPp.exists_elim fun b35 => ?_
      rw [memRegion_16_ret_split ret]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWPp.exists_elim fun rv1 => SepWPp.exists_elim fun rv2 => ?_
      simp only [DefsBudget.optSerializeAddressesAt, serializeAddresses, hs, hr,
        Option.bind_eq_bind, Option.bind, Pure.pure,
        optSerializeAddressesAt_some_36_eq, A.repAlloc_live_norm,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
      wp_done

theorem serialize_addresses_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {parse : UuidParser}
    {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim parse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := allocHookStack) (by decide)
    (parseSidCellsBudget_of_parseSidCode hparse)
    (shimBudgetWithStack_of_noAllocShim allocHookStack (mac_ls_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc mac_ls_externAt?_of_mem
      (by decide) (by decide))

theorem serialize_addresses_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack)))
    (hshim : HookSat H lsMacRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim uuidTryParse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := parseSidStack + extHookStack) (by decide)
    (parseSidCellsBudget_of_parseSidStack hparse)
    (shimBudgetSpecWithStack_widen (by decide)
      (shimBudgetWithStack_of_noAllocShim extHookStack (mac_ls_hook_ok_of_mem hshim)))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc mac_ls_externAt?_of_mem
      (by decide) (by decide))

theorem serialize_addresses_placed_ok_of_rustAllocShimVm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {parse : UuidParser}
    {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec parse)))
    (hshim : HookSat H lsMacRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim parse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := allocHookStack) (by decide)
    (parseSidCellsBudget_of_parseSidCode hparse)
    (shimBudgetWithStack_of_noAllocShim allocHookStack
      (new_shim_placed_ok_of_rustAllocShimVm hshim
        (prog := (blkPC_61).rebase (blkPl_61).base H) (i := 61)))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc mac_ls_externAt?_of_mem
      (by decide) (by decide))

theorem serialize_addresses_placed_ok_x_of_rustAllocShimVm [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hparse : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeStackBudgetSpec extHookStack)))
    (hshim : HookSat H lsMacRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsMacRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim uuidTryParse)) :=
  serialize_addresses_placed_ok_of_hooks (callStack := parseSidStack + extHookStack) (by decide)
    (parseSidCellsBudget_of_parseSidStack hparse)
    (shimBudgetSpecWithStack_widen (by decide)
      (shimBudgetWithStack_of_noAllocShim extHookStack
        (new_shim_placed_ok_of_rustAllocShimVm hshim
          (prog := (blkPC_61).rebase (blkPl_61).base H) (i := 61))))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc mac_ls_externAt?_of_mem
      (by decide) (by decide))

end LibsignalBinary.Proofs.TripleRatchet.Mac.AddressesBudget
