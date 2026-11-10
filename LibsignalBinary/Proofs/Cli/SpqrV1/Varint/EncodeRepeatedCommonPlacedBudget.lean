/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Step Helpers for `encode_repeated [local#3]` (Block `448`)

Threads `RustCliAllocBudget` and `VmPreserved` through the loop-body step helpers for
`encode_repeated::<Vec<u8>, Vec<u8>> [local#3]` (Block `448`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeBytesField encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym)
open CryptoVerification.SpqrV1.Varint
  (EncRepeatedCalleeSavedPlaced base_add16_add24 base_add16_sub8 base_add16_sub8_add8
   elem_len_after_reserve_not_ult elem_len_ult_spare_iff encodeBytesField_some_eq
   encodeBytesField_some_length encodeKey_lengthDelimited_eq encodeRepeatedBytes
   encodeVarint_length_bounds latch_beq_zero_true latch_sub24_eq len_beq_zero_false
   repeatedBytesElemAt vecU8At_eq_header_rest vecU8At_expose_slice
   vecU8At_of_header_rest vecU8At_pack_slice withEncRepeatedCSPlaced)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_448 lsProg_448)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved fitsEvents_append)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedElemStep pushBytesStep pushBytesStep_snd_eq reserveStep
   reserveStep_of_need_doReserveEvents reserveStep_of_spare
   sepWP_done_tpidr_placed sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedPlacedCommonBudget
  (step_do_reserve2_call_gen_placed step_encode_varint_det_call_gen_placed
   step_memcpy_call_gen_placed)

private theorem latch_sub24_eq_59 (k : Nat) (hlt : k + 1 < 2 ^ 59) :
    BitVec.ofNat 64 (24 * (k + 1)) - 24#64 = BitVec.ofNat 64 (24 * k) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 24 * (k + 1) < 2 ^ 64 := by omega
  have h2 : 24 * k < 2 ^ 64 := by omega
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    change 24 * (k + 1) - 24 = 24 * k
    omega
  · rw [BitVec.le_def]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
    omega

attribute [local irreducible] Program.externAt? Program.fnAddr
  encodeVarint encodeBytesField encodeRepeatedBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeRepeated1

/-- Copy block (`56..84`) on Block `448`: copies `elemBs` (`elemBs ≠ []`) from `elemPtr`
to `ptr + bs2.length` via `memcpy` (`sessionMemcpyRegionBudgetSpec`), updates `[v + 16]`
to `bs2.length + elemBs.length` via `by_vm_steps`, and preserves `A.pool lim curSt` and `VmPreserved`. -/
theorem step_copy_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (v cap ptr elemPtr sp keyVal remBytes curBase16 : BitVec 64)
    (bs2 elemBs : List (BitVec 8)) (curSt : M.σ)
    (hle : bs2.length + elemBs.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0)
    (hne : elemBs ≠ [])
    {s0 s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 56#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 elemBs.length)
    (hx22 : s.readReg64 .x22 = elemPtr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 bs2.length)
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase16)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v cap ptr bs2 ∗ (elemPtr ↦ₛ elemBs) ∗ A.pool lim curSt s) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase16 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_448 H) ret sm
        ((vecU8At A.repAlloc v cap ptr (bs2 ++ elemBs) ∗ (elemPtr ↦ₛ elemBs) ∗
          A.pool lim curSt sm) ∗ F) Q Qp) :
    SepWPp (lsProg_448 H) ret s P Q Qp := by
  subst hP
  have hpos : 0 < elemBs.length := List.length_pos_of_ne_nil hne
  rw [vecU8At_expose_slice A.repAlloc v cap ptr bs2 elemBs.length hle hcap hptr hpos]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsρ spqrMemcpySym)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm0 _hinv0
    rw [← A.pool_of_vmPreserved hvm0]
    have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine step_memcpy_call_gen_placed A lim hmemcpy
      (ptr + BitVec.ofNat 64 bs2.length) elemPtr sp ((blkPl_448).base + 76#64) elemBs curSt
      (F := (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
        A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs2) ∗
        memRegion (ptr + BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 elemBs.length)
          (cap.toNat - bs2.length - elemBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by sep_ac_rfl) ?_
    intro sm hpcm1 hrunm1 hspm1 htrm1 hcsm1 hcs_s0 hvm_mc
    rcases hcsm1 with ⟨hx19m, hx20m, hx21m, _, hx23m, hx24m, hx25m, _⟩
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 84#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm1 _hinv1
      rw [← A.pool_of_vmPreserved hvm1]
      refine SepWPp.weaken_pre ?_
        (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (hcs_s0.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
          (hvm0.trans (hvm_mc.trans hvm1)))
      rw [← vecU8At_pack_slice A.repAlloc v cap ptr bs2 elemBs hle hcap hptr hne]
      exact Entails.of_eq (by sep_ac_rfl)))

/-- Single element iteration (`96..184 → 84`) on Block `448`:
encodes `encodeBytesField tag (some elemBs)` for `(elemPtr, elemBs)` at `curBase`,
advances capacity and cost-model state along
`encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs`, and stops at loop latch
`(blkPl_448).base + 84#64`. -/
theorem step_iter_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 80 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (henc : subroutine_ok (lsProg_448 H) (lsmpl.base 451)
      (withEncRepeatedCSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_448 H) (lsmpl.base 460)
      (withEncRepeatedCSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (hmemcpy : subroutine_ok (lsProg_448 H) (lsρ spqrMemcpySym) sessionMemcpyRegionBudgetSpec)
    (tag : Nat)
    (v curCap curPtr curBase elemPtr sp remBytes : BitVec 64)
    (curBs elemBs : List (BitVec 8)) (curSt : M.σ)
    (hfit : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat ∨
      curBs.length + (encodeBytesField tag (some elemBs)).length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt
      (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_448).base + 96#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2))
    (hx24 : s.readReg64 .x24 = remBytes)
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hP : P = (repeatedBytesElemAt curBase elemPtr elemBs ∗
      vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 80#64) (48 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_448).base + 84#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x24 = remBytes →
      sm.readReg64 .x25 = curBase + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 →
      SepWPp (lsProg_448 H) ret sm
        ((repeatedBytesElemAt curBase elemPtr elemBs ∗
          vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeBytesField tag (some elemBs)) ∗
          A.pool lim
            (M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt) sm ∗
          stackAt (sp - 80#64) (48 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_448 H) ret s P Q Qp := by
  have hcopy_step := step_copy_placed A lim H hmemcpy
  subst hP
  have hlen_ef := encodeBytesField_some_length tag elemBs
  have hkey_eq := encodeKey_lengthDelimited_eq tag
  have hkey_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 (tag * 8 + 2))
  have hlen_bounds := encodeVarint_length_bounds (BitVec.ofNat 64 elemBs.length)
  let keyVal := BitVec.ofNat 64 (tag * 8 + 2)
  let lenVal := BitVec.ofNat 64 elemBs.length
  let step1 := pushBytesStep (encodeVarint keyVal).length curCap.toNat curBs.length
  let step2 := pushBytesStep (encodeVarint lenVal).length step1.1
    (curBs.length + (encodeVarint keyVal).length)
  let step3 := reserveStep step2.1
    (curBs.length + (encodeVarint keyVal).length + (encodeVarint lenVal).length) elemBs.length
  have helemStep_fst :
      (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 = step3.1 := rfl
  have helemStep_snd :
      (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 =
        step1.2 ++ step2.2 ++ step3.2 := rfl
  rw [helemStep_snd, fitsEvents_append, fitsEvents_append] at hfits
  rcases hfits with ⟨⟨hfits1, hfits2⟩, hfits3⟩
  have hfits1_ev :
      FitsEvents M lim curSt
        (encodeVarintEvents (EncodeVarintGhost.mk keyVal v curCap curPtr curBs)) := by
    rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
    exact hfits1
  have hfit1 : curBs.length + (encodeVarint keyVal).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62 := by
    dsimp only [keyVal]
    rw [← hkey_eq]
    rcases hfit with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hb8 := base_add16_sub8 curBase
  have hb16 := base_add16_sub8_add8 curBase
  rw [repeatedBytesElemAt]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hvm0 _hinv0
    rw [← A.pool_of_vmPreserved hvm0]
    refine step_encode_varint_det_call_gen_placed A lim henc
      keyVal v curCap curPtr sp ((blkPl_448).base + 112#64) curBs curSt hfit1 hfits1_ev
      (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ lenVal) ∗
        (elemPtr ↦ₛ elemBs) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [keyVal, arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
      (by sep_ac_rfl) ?_
    intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hcsm1 hcs1 hge1 hpres1 hcap1_det
    rcases hcsm1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, _, hx24_1, hx25_1, _⟩
    have hcap1_step : cap1.toNat = step1.1 := hcap1_det
    have hfit2 : (curBs ++ encodeVarint keyVal).length +
        (encodeVarint lenVal).length ≤ cap1.toNat ∨
        (curBs ++ encodeVarint keyVal).length + 10 < 2 ^ 62 := by
      dsimp only [keyVal, lenVal]
      rw [List.length_append, ← hkey_eq]
      rcases hfit with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have hfits2_ev :
        FitsEvents M lim (M.stepEvents step1.2 curSt)
          (encodeVarintEvents
            (EncodeVarintGhost.mk lenVal v cap1 ptr1 (curBs ++ encodeVarint keyVal))) := by
      rw [encodeVarintEvents, ← pushBytesStep_snd_eq]
      simp only [List.length_append, hcap1_step]
      exact hfits2
    apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 451)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hvm1 _hinv1
      rw [← A.pool_of_vmPreserved hvm1]
      refine step_encode_varint_det_call_gen_placed A lim henc
        lenVal v cap1 ptr1 sp ((blkPl_448).base + 124#64)
        (curBs ++ encodeVarint keyVal) (M.stepEvents step1.2 curSt) hfit2 hfits2_ev
        (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ lenVal) ∗
          (elemPtr ↦ₛ elemBs) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [lenVal, arm64_norm, *]) (by simp only [arm64_norm, *])
        (hcs1.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
        (by sep_ac_rfl) ?_
      intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hcsm2 hcs2 hge2 hpres2 hcap2_det
      rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, _, hx24_2, hx25_2, _⟩
      have hcap2_step : cap2.toNat = step2.1 := by
        simpa only [List.length_append, hcap1_step] using hcap2_det
      have hstep2_ev :
          (pushBytesStep (encodeVarint lenVal).length cap1.toNat
            (curBs ++ encodeVarint keyVal).length).2 = step2.2 := by
        simp only [List.length_append, hcap1_step, step2]
      rw [hstep2_ev]
      set bs2 := curBs ++ encodeVarint keyVal ++ encodeVarint lenVal with hbs2_def
      have hstep3_cap :
          step3 = reserveStep cap2.toNat bs2.length elemBs.length := by
        have hbs2_len_eq : bs2.length =
            curBs.length + (encodeVarint keyVal).length + (encodeVarint lenVal).length := by
          simp only [hbs2_def, List.length_append]
        dsimp only [step3]
        rw [← hcap2_step, ← hbs2_len_eq]
      have hbs_final : bs2 ++ elemBs = curBs ++ encodeBytesField tag (some elemBs) := by
        simp only [hbs2_def, keyVal, lenVal, ← hkey_eq, encodeBytesField_some_eq, List.append_assoc]
      have hbs2_len : bs2.length + elemBs.length =
          curBs.length + (encodeBytesField tag (some elemBs)).length := by
        rw [← List.length_append, hbs_final, List.length_append]
      clear_value bs2
      clear hbs2_def hcap1_det hcap1_step hcap2_det hcap2_step
      rw [vecU8At_eq_header_rest A.repAlloc v cap2 ptr2 bs2]
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hbs2_le, hcap2_lt, hptr2_ne⟩ => ?_
      have helem_lt : elemBs.length < 2 ^ 63 := by
        rcases hfit with h | h <;> omega
      by_cases hneed : cap2.toNat < bs2.length + elemBs.length
      · have hfit3 : bs2.length + elemBs.length < 2 ^ 62 := by
          rcases hfit with h | h <;> omega
        have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = true :=
          (elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mpr hneed
        have hne : elemBs ≠ [] := by
          intro h; subst h; simp at hneed; omega
        obtain ⟨hnot_ult, hnew_ge, hnew_cap, hnew_bound⟩ := elem_len_after_reserve_not_ult hfit3 hneed
        have hstep3_eq :
            step3 =
              (reserveCap cap2.toNat bs2.length elemBs.length,
               doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length)) := by
          rw [hstep3_cap]
          exact reserveStep_of_need_doReserveEvents v cap2 ptr2 bs2 elemBs.length (by omega)
        have hfits3_dr :
            FitsEvents M lim (M.stepEvents step2.2 (M.stepEvents step1.2 curSt))
              (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length)) := by
          rw [← AllocCostModel.stepEvents_append]
          simpa only [congrArg Prod.snd hstep3_eq] using hfits3
        apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm2 _hinv2
          rw [← A.pool_of_vmPreserved hvm2]
          have hx1_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hx2_toNat : (BitVec.ofNat 64 elemBs.length).toNat = elemBs.length := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine step_do_reserve2_call_gen_placed hres A lim hdoReserve
            v cap2 ptr2 sp ((blkPl_448).base + 168#64) bs2 elemBs.length
            (M.stepEvents step2.2 (M.stepEvents step1.2 curSt)) hnew_bound hfits3_dr
            (F := ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ lenVal) ∗
              (elemPtr ↦ₛ elemBs) ∗ F)
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) halign
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *])
            (hcs2.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
            (by rw [← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]; sep_ac_rfl) ?_
          intro s3 newPtr hpc3 hrun3 hsp3 htr3 hcsm3 hcs3
          rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, _, hx24_3, hx25_3, _⟩
          rw [vecU8At_eq_header_rest A.repAlloc v
            (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr bs2]
          simp only [sepConj_assoc]
          refine SepWPp.pure_elim fun ⟨hnew_le, hnew_lt63, hnew_ptr⟩ => ?_
          apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 56#64)
          by_vm_steps (
            wp_steps
            apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, wp_norm, *])
            intro hvm3 _hinv3
            rw [← A.pool_of_vmPreserved hvm3]
            refine hcopy_step v (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length))
              newPtr elemPtr sp keyVal remBytes (curBase + 16#64) bs2 elemBs
              (M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length))
                (M.stepEvents step2.2 (M.stepEvents step1.2 curSt)))
              hnew_ge hnew_lt63 hnew_ptr hne
              (F := stackAt (sp - 80#64) (48 + resStack) ∗
                ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ lenVal) ∗ F)
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) halign
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [keyVal, arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (hcs3.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
              (by
                rw [← vecU8At_of_header_rest A.repAlloc v
                  (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length))
                  newPtr bs2 hnew_le hnew_lt63 hnew_ptr]
                sep_ac_rfl) ?_
            intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4 _hvm4
            have hst_final :
                M.stepEvents (doReserveEvents (DoReserveCall.mk v cap2 ptr2 bs2 elemBs.length))
                  (M.stepEvents step2.2 (M.stepEvents step1.2 curSt)) =
                M.stepEvents
                  (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt := by
              rw [helemStep_snd, AllocCostModel.stepEvents_append,
                AllocCostModel.stepEvents_append, congrArg Prod.snd hstep3_eq]
            have hcap_final :
                (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)).toNat =
                  (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 := by
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), helemStep_fst,
                congrArg Prod.fst hstep3_eq]
            rw [hst_final]
            refine SepWPp.weaken_pre ?_
              (hnext s4 (BitVec.ofNat 64 (reserveCap cap2.toNat bs2.length elemBs.length)) newPtr
                hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
                (by omega) (fun h => absurd h (by omega)) hcap_final)
            rw [hbs_final, repeatedBytesElemAt]
            exact Entails.of_eq (by sep_ac_rfl)))
      · have hle2 : bs2.length + elemBs.length ≤ cap2.toNat := by omega
        have hstep3_eq : step3 = (cap2.toNat, []) := by
          rw [hstep3_cap]
          exact reserveStep_of_spare hle2
        have hst_spare :
            M.stepEvents step2.2 (M.stepEvents step1.2 curSt) =
              M.stepEvents (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).2 curSt := by
          rw [helemStep_snd, congrArg Prod.snd hstep3_eq, List.append_nil,
            AllocCostModel.stepEvents_append]
        have hcap_spare :
            cap2.toNat = (encodeRepeatedElemStep tag curCap.toNat curBs.length elemBs).1 := by
          rw [helemStep_fst, congrArg Prod.fst hstep3_eq]
        have hhi : (cap2 - BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 elemBs.length) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact hneed ((elem_len_ult_spare_iff hbs2_le hcap2_lt helem_lt).mp h)
        have hpres_all : curBs.length + (encodeBytesField tag (some elemBs)).length ≤ curCap.toNat →
            cap2 = curCap ∧ ptr2 = curPtr := by
          intro hfit_cap
          have h1 : curBs.length + (encodeVarint keyVal).length ≤ curCap.toNat := by
            dsimp only [keyVal]; rw [← hkey_eq]; omega
          obtain ⟨hc1, hp1⟩ := hpres1 h1
          have h2 : (curBs ++ encodeVarint keyVal).length +
              (encodeVarint lenVal).length ≤ cap1.toNat := by
            dsimp only [keyVal, lenVal]; rw [hc1, List.length_append, ← hkey_eq]; omega
          obtain ⟨hc2, hp2⟩ := hpres2 h2
          exact ⟨hc2.trans hc1, hp2.trans hp1⟩
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 144#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, wp_norm, *])
          intro hvm2 hinv2
          rw [← A.pool_of_vmPreserved hvm2]
          by_cases helem : elemBs = []
          · subst helem
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 84#64)
            by_vm_steps (
              wp_steps
              apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hvm3 hinv3
              rw [← A.pool_of_vmPreserved hvm3, hst_spare]
              refine SepWPp.weaken_pre ?_
                (hnext _ cap2 ptr2
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                  (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                    (by simp only [arm64_norm]) (hinv2.trans hinv3))
                  (by omega) hpres_all hcap_spare)
              have hbs_nil : bs2 = curBs ++ encodeBytesField tag (some []) := by
                simpa using hbs_final
              rw [← hbs_nil, ← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne,
                repeatedBytesElemAt]
              exact Entails.of_eq (by sep_ac_rfl))
          · have hcbnz : (BitVec.ofNat 64 elemBs.length == 0#64) = false :=
              len_beq_zero_false (List.length_pos_of_ne_nil helem) helem_lt
            apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 56#64)
            by_vm_steps (
              wp_steps
              apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, wp_norm, *])
              intro hvm3 hinv3
              rw [← A.pool_of_vmPreserved hvm3]
              refine hcopy_step v cap2 ptr2 elemPtr sp
                keyVal remBytes (curBase + 16#64) bs2 elemBs
                (M.stepEvents step2.2 (M.stepEvents step1.2 curSt))
                hle2 hcap2_lt hptr2_ne helem
                (F := stackAt (sp - 80#64) (48 + resStack) ∗
                  ((curBase + 8#64) ↦₆₄ elemPtr) ∗ ((curBase + 16#64) ↦₆₄ lenVal) ∗ F)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) halign
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [keyVal, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (hcs2.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
                  (by simp only [arm64_norm]) (hinv2.trans hinv3))
                (by
                  rw [← vecU8At_of_header_rest A.repAlloc v cap2 ptr2 bs2 hbs2_le hcap2_lt hptr2_ne]
                  sep_ac_rfl) ?_
              intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4 _hvm4
              rw [hst_spare]
              refine SepWPp.weaken_pre ?_
                (hnext s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hx24_4 hx25_4 hcs4
                  (by omega) hpres_all hcap_spare)
              rw [hbs_final, repeatedBytesElemAt]
              exact Entails.of_eq (by sep_ac_rfl)))))

/-- Latch block for the final element (`84..92 → 212`) on Block `448`, exposing `VmPreserved`. -/
theorem step_latch_zero_placed [LibsignalPlacement] (H : String → Option (State → State))
    (sp curBase : BitVec 64)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * 1))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 212#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      EncRepeatedCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_448 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_448 H) ret s P Q Qp oom := by
  have hbeq := latch_beq_zero_true
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 212#64)
  wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hvmp _hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
    hvmp

/-- Latch block when `k > 0` elements remain (`84..92 → 96`, `k + 1 < 2 ^ 59`) on Block `448`,
exposing `VmPreserved`. -/
theorem step_latch_succ_59_placed [LibsignalPlacement] (H : String → Option (State → State))
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 59)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 96#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_448 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_448 H) ret s P Q Qp oom := by
  have hbeq : (BitVec.ofNat 64 (24 * (k + 1)) == 24#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change 24 * (k + 1) = 24 at ht
    omega
  have hx24_next := latch_sub24_eq_59 k hlt
  have hx25_next := base_add16_add24 curBase
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base + 96#64)
  wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hvmp _hinv0
  exact hnext _
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans (by simp only [EncRepeatedCalleeSavedPlaced, arm64_norm, *, and_self]))
    hvmp

/-- Latch block when `k > 0` elements remain (`84..92 → 96`, `k + 1 < 2 ^ 58`) on Block `448`,
exposing `VmPreserved`. -/
theorem step_latch_succ_placed [LibsignalPlacement] (H : String → Option (State → State))
    (v keyVal sp curBase : BitVec 64) (k : Nat) (hpos : 0 < k) (hlt : k + 1 < 2 ^ 58)
    {s0 s : State} {ret : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_448).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 80#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = keyVal)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (24 * (k + 1)))
    (hx25 : s.readReg64 .x25 = curBase + 16#64)
    (hcs : EncRepeatedCalleeSavedPlaced s0 s)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_448).base + 96#64 →
      sm.status = .Running →
      sm.sp = sp - 80#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = keyVal →
      sm.readReg64 .x24 = BitVec.ofNat 64 (24 * k) →
      sm.readReg64 .x25 = (curBase + 24#64) + 16#64 →
      EncRepeatedCalleeSavedPlaced s0 sm →
      VmPreserved s sm →
      SepWPp (lsProg_448 H) ret sm P Q Qp oom) :
    SepWPp (lsProg_448 H) ret s P Q Qp oom :=
  step_latch_succ_59_placed H v keyVal sp curBase k hpos
    (Nat.lt_trans hlt (by decide)) hpc hrun hsp htr hx19 hx20 hx24 hx25 hcs hnext

end EncodeRepeated1

end LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommonPlacedBudget
