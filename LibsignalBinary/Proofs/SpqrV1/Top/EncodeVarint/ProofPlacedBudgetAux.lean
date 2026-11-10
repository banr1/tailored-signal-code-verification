/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stages 3..6 for `spqr::encode_varint` (`Block 326`)

Proves budget-threaded continuation-byte stages 3..6 (`+204..+508`) for `spqr::encode_varint`
(`Block 326`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlacedBudgetAux

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (growOneU8Events)
open CryptoVerification
  (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (cap_eq_ofNat_len sepWPp_extract_vecU8Buf_le varintContByte vecU8Buf
   vecU8Buf_eq_open_one vecU8Buf_snoc_eq)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Top.EncodeVarint
  (SpqrEncVarintCalleeSavedPlaced len_beq_cap_false origLen_add_step)
open CryptoVerification.SpqrV1.Top.Placed
  (blkPC_326 blkPl_326)
open scoped CryptoVerification.SpqrV1.Top.EncodeVarint
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
  (sepWPp_of_sepWP_cs_placed_vm)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget
  (growOneU8ByteStep)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget
  (GrowOneU8StepOkExt)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.BasePlacedBudget
  (growOneU8ByteStep_of_eq growOneU8ByteStep_of_lt
   grow_frame_budget_reassoc step_growOneU8_placed_call)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Continuation-Byte Stages 3..6 -/

/-- Stage 3 (`+204..+256`): appends `varintContByte (val >>> 14)` and branches on
`(val >>> 21).ult 128#64` to `+256` (`exit3`) or `+276` (Stage 4), setting `x23 = val >>> 28`. -/
theorem step_spqrEncVarint_placed_s3 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (horig : origLen + 2#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 204#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 21).ult 128#64 then
        (blkPl_326).base + 256#64
      else
        (blkPl_326).base + 276#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 28 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 14)]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 21).ult 128#64 = true ∨ (val >>> 21).ult 128#64 = false := by
    cases (val >>> 21).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 14)) 2#64 3#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 256#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 276#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 14)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 232#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m _ hx24m _ hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
      have hx24m' : BitVec.zeroExtend 8 (sm.readReg64 .x24) = varintContByte (val >>> 14) := by
        rw [hx24m]; simp only [arm64_norm, *]
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 256#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 276#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 14)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

/-- Stage 4 (`+276..+328`): appends `varintContByte (val >>> 21)` and branches on
`(val >>> 28).ult 128#64` to `+328` (`exit_328`) or `+348` (Stage 5), setting `x24 = val >>> 35`. -/
theorem step_spqrEncVarint_placed_s4 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (horig : origLen + 3#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 276#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 28)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 28).ult 128#64 then
        (blkPl_326).base + 328#64
      else
        (blkPl_326).base + 348#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 28 →
      sm.readReg64 .x24 = val >>> 35 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 21)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 21)]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 28).ult 128#64 = true ∨ (val >>> 28).ult 128#64 = false := by
    cases (val >>> 28).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 21)) 3#64 4#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 328#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 21)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 348#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 21)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 304#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ hx25m hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
      have hx23m' : sm.readReg64 .x23 = val >>> 28 := by simp only [arm64_norm, *]
      have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 21) := by
        rw [hx25m]; simp only [arm64_norm, *]
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 328#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 21)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 348#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 21)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

/-- Stage 5 (`+348..+396`): appends `varintContByte (val >>> 28)` and branches on
`(val >>> 35).ult 128#64` to `+396` (`exit_396`) or `+460` (Stage 6), setting `x23 = val >>> 42`. -/
theorem step_spqrEncVarint_placed_s5 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (horig : origLen + 4#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 348#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 28)
    (hx24 : s.readReg64 .x24 = val >>> 35)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 35).ult 128#64 then
        (blkPl_326).base + 396#64
      else
        (blkPl_326).base + 460#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 42 →
      sm.readReg64 .x24 = val >>> 35 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 28)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 28)]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 35).ult 128#64 = true ∨ (val >>> 35).ult 128#64 = false := by
    cases (val >>> 35).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 28)) 4#64 5#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 396#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 28)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 460#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 28)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 372#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m _ hx24m hx25m hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
      have hx24m' : sm.readReg64 .x24 = val >>> 35 := by simp only [arm64_norm, *]
      have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 28) := by
        rw [hx25m]; simp only [arm64_norm, *]
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 396#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 28)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 460#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 28)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

/-- Stage 6 (`+460..+508`): appends `varintContByte (val >>> 35)` and branches on
`(val >>> 42).ult 128#64` to `+328` (`exit_328`) or `+508` (Stage 7), setting `x24 = val >>> 49`. -/
theorem step_spqrEncVarint_placed_s6 [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (abs : String → Option (State → State))
    {s0 s : State} (hgrow : GrowOneU8StepOkExt s0 A lim abs)
    (val v origLen curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (horig : origLen + 5#64 = BitVec.ofNat 64 curBs.length)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    (hfits_grow : curCap.toNat = curBs.length → FitsEvents M lim curSt (growOneU8Events curCap))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_326).base + 460#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = val)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 curBs.length)
    (hx22 : s.readReg64 .x22 = origLen)
    (hx23 : s.readReg64 .x23 = val >>> 42)
    (hx24 : s.readReg64 .x24 = val >>> 35)
    (hcs : SpqrEncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A.repAlloc curCap curPtr curBs ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (if (val >>> 42).ult 128#64 then
        (blkPl_326).base + 328#64
      else
        (blkPl_326).base + 508#64) →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = val →
      sm.readReg64 .x21 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length →
      sm.readReg64 .x22 = origLen →
      sm.readReg64 .x23 = val >>> 42 →
      sm.readReg64 .x24 = val >>> 49 →
      SpqrEncVarintCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap = (growOneU8ByteStep curCap curBs.length).1 →
      SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) sm
        (((v ↦₆₄ nextCap) ∗ ((v + 8#64) ↦₆₄ nextPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 35)]).length) ∗
          vecU8Buf A.repAlloc nextCap nextPtr (curBs ++ [varintContByte (val >>> 35)]) ∗
          A.pool lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt) sm ∗
          stackAt (sp - 80#64) extHookStack) ∗ F)
        Q Qp) :
    SepWPp ((blkPC_326).rebase (blkPl_326).base (Rust.withPanics abs)) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A.repAlloc) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      A.pool lim curSt s ∗ stackAt (sp - 80#64) extHookStack ∗ F)
    (by sep_ac_rfl) fun hle => ?_
  have hcond_or : (val >>> 42).ult 128#64 = true ∨ (val >>> 42).ult 128#64 = false := by
    cases (val >>> 42).ult 128#64 <;> simp
  have hlen1 := origLen_add_step (varintContByte (val >>> 35)) 5#64 6#64 rfl horig
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := len_beq_cap_false hlt
    have hstep_lt := growOneU8ByteStep_of_lt hlt
    have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt = curSt := by
      rw [hstep_lt]; rfl
    rw [vecU8Buf_eq_open_one A.repAlloc curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    rcases hcond_or with hcond | hcond
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 328#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 35)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
    · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 508#64)
      by_vm_steps
        wp_steps
        refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
        rw [vecU8Buf_snoc_eq A.repAlloc curCap curPtr curBs (varintContByte (val >>> 35)) hlt,
          ← A.pool_of_vmPreserved hvm, ← hst_eq]
        exact hnext _ curCap curPtr
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
          (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (by rw [hstep_lt])
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    have hstep_eq := growOneU8ByteStep_of_eq hcap_eq
    apply sepWPp_of_sepWP_cs_placed_vm (mid := lsmpl.base 619)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, *], fun hvm hinv_step => ?_⟩
      rw [← A.pool_of_vmPreserved hvm]
      refine step_growOneU8_placed_call A lim abs hgrow v curCap curPtr sp
        ((blkPl_326).base + 484#64) curBs curSt hcap_eq (hlen_lt.resolve_left hlt)
        (hfits_grow hcap_eq)
        (F := ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (hcs.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro sm newCap p' hpcm hrunm hspm htrm hx19m hx20m hx21m hx22m hx23m _ hx25m hcsm hnew_gt hnew_ge hnew_eq
      have hx19m' : sm.readReg64 .x19 = v := by simp only [arm64_norm, *]
      have hx20m' : sm.readReg64 .x20 = val := by simp only [arm64_norm, *]
      have hx21m' : sm.readReg64 .x21 = BitVec.ofNat 64 curBs.length := by simp only [arm64_norm, *]
      have hx22m' : sm.readReg64 .x22 = origLen := by simp only [arm64_norm, *]
      have hx23m' : sm.readReg64 .x23 = val >>> 42 := by simp only [arm64_norm, *]
      have hx25m' : BitVec.zeroExtend 8 (sm.readReg64 .x25) = varintContByte (val >>> 35) := by
        rw [hx25m]; simp only [arm64_norm, *]
      have hst_eq : M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt =
          M.stepEvents (growOneU8Events curCap) curSt := by
        rw [hstep_eq]
      rw [vecU8Buf_eq_open_one A.repAlloc newCap p' curBs hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      rcases hcond_or with hcond | hcond
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 328#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 35)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])
      · apply sepWPp_of_sepWP_cs_placed_vm (mid := (blkPl_326).base + 508#64)
        by_vm_steps
          wp_steps
          refine SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            ⟨by simp only [arm64_norm, *], fun hvm2 hinv_step2 => ?_⟩
          rw [vecU8Buf_snoc_eq A.repAlloc newCap p' curBs (varintContByte (val >>> 35)) hnew_gt,
            ← A.pool_of_vmPreserved hvm2, ← hst_eq,
            grow_frame_budget_reassoc A lim (M.stepEvents (growOneU8ByteStep curCap curBs.length).2 curSt)]
          exact hnext _ newCap p'
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (hcsm.trans (by simp only [SpqrEncVarintCalleeSavedPlaced, arm64_norm, *, and_self]))
            hnew_ge (fun h => absurd h hlt) (by rw [hstep_eq, hnew_eq])

end LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlacedBudgetAux
