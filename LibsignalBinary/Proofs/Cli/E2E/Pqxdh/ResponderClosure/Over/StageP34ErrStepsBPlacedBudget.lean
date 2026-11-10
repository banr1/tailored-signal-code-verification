/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsBPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed 1-Element `previous_sessions` Stage P4 `Ok` Drop Basic Block

Proves the budget-threaded `[LibsignalPlacement]` Stage P4 `Ok` epilogue
`p4_seg4e_prev1_of_dealloc_placed_wp` (`+0x048c → retAddr`) on `lsProg_518 ext`, dropping a 1-element
`prevVecAt [enc]` along `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsBPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.RustHeap (
  LayoutOk RustAlloc allocHookStack vecBuf vecHeader vecU8 vecU8At_entails_dealloc
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  HdrP hdrP_coro_eq prevVecAt prevVecAt_eq prevVecAt_one_eq
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsAPlacedBudget (
  dpClosureEntryP34Placed
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Spatial Split/Merge and `FreeOnlyEvs` Pool Helpers -/

private theorem entails_replace_sub_p34_pl {P B B' F Q : SepProp}
    (hB : B ⊢ B') (hP : P = B ∗ F) (hQ : Q = B' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hB

private theorem prevVecAt_one_drop_split_p34_pl (A : RustAlloc) (r cap q : BitVec 64)
    (enc : List (BitVec 8)) (hcap : cap ≠ 0#64) :
    prevVecAt A r cap q [enc] ⊢
      ∃∗ c : BitVec 64, ∃∗ p : BitVec 64,
        ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗
        HdrP r cap q 1#64 ∗
        A.live q (cap.toNat * 24) 8 ∗
        (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat) ∗
        memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
  have h0 : prevVecAt A r cap q [enc] ⊢
      HdrP r cap q 1#64 ∗ ⌜1 ≤ cap.toNat ∧ cap.toNat * 24 < 2 ^ 63 ∧ q ≠ 0#64⌝ ∗
      A.live q (cap.toNat * 24) 8 ∗
      (∃∗ c : BitVec 64, ∃∗ p : BitVec 64, (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
        ⌜c.toNat < 2 ^ 63⌝ ∗ (if c = 0#64 then emp else A.live p c.toNat 1 ∗ memRegion p c.toNat)) ∗
      memRegion (q + 24#64) ((cap.toNat - 1) * 24) := by
    rw [prevVecAt_one_eq A r cap q enc hcap]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))
    unfold vecU8
    refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
    refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
    refine Entails.trans (vecU8At_entails_dealloc A q c p enc) ?_
    unfold vecHeader
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right ?_)
    refine sepConj_mono (pointsTo64_entails_memRegion (q + 16#64) _) ?_
    exact Entails.pure_left fun h => Entails.pure_right h.2.1 (Entails.refl _)
  refine Entails.trans h0 ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun c => Entails.sepExists_right c ?_
  refine Entails.sepExists_elim fun p => Entails.sepExists_right p ?_
  exact Entails.of_eq (by sep_ac_rfl)

private theorem prevVec1_outer_merge_p34_pl (q c p : BitVec 64) (cap : Nat)
    (h : 1 ≤ cap ∧ cap * 24 < 2 ^ 63) :
    (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗ memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q (cap * 24) := by
  have h24 : (q ↦₆₄ c) ∗ ((q + 8#64) ↦₆₄ p) ∗ memRegion (q + 16#64) 8 ∗
      memRegion (q + 24#64) ((cap - 1) * 24) ⊢
      memRegion q 24 ∗ memRegion (q + 24#64) ((cap - 1) * 24) := by
    rw [ProofLib.memRegion_split' (b := q) (b' := q + 8#64) (N := 24) (n := 8) (k := 16)
          rfl rfl (by decide),
        ProofLib.memRegion_split' (b := q + 8#64) (b' := q + 16#64) (N := 16) (n := 8) (k := 8)
          rfl (by bv_omega) (by decide)]
    simp only [sepConj_assoc]
    exact sepConj_mono (pointsTo64_entails_memRegion q c)
      (sepConj_mono (pointsTo64_entails_memRegion (q + 8#64) p) (Entails.refl _))
  refine Entails.trans h24 ?_
  rw [ProofLib.memRegion_split' (b := q) (b' := q + 24#64) (N := cap * 24) (n := 24)
        (k := (cap - 1) * 24) (by omega) rfl (by omega)]
  exact Entails.refl _

private theorem prevVecAt_one_cap0_false_p34_pl (A : RustAlloc) (r q : BitVec 64)
    (enc : List (BitVec 8)) :
    prevVecAt A r 0#64 q [enc] ⊢ ⌜False⌝ := by
  rw [prevVecAt_eq]
  unfold vecBuf
  rw [sepConj_left_comm]
  refine Entails.pure_left fun ⟨hlen, _, _⟩ => ?_
  nomatch hlen

private theorem sepWP_exists_elim_p34_pl {α : Sort _} {prog : Program} {pc : BitVec 64} {s : State}
    {P : α → SepProp} {post : State → SepProp → Prop}
    (h : ∀ a, SepWP prog pc s (P a) post) :
    SepWP prog pc s (∃∗ a, P a) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, ha⟩ := hm
  exact h a R ha

private theorem sepWP_pure_elim_p34_pl {prog : Program} {pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog pc s P post) :
    SepWP prog pc s (⌜φ⌝ ∗ P) post := by
  unfold SepWP at h ⊢
  intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2

private theorem pool_entails_freeOnly_one {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sz al : Nat) (s1 : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz al) st) s1 ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1 :=
  Entails.sepExists_right (rustDeallocEvents sz al)
    (Entails.pure_right (FreeOnlyEvs.singleton al sz) (Entails.refl _))

private theorem pool_entails_freeOnly_two {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (sz1 al1 sz2 al2 : Nat) (s1 : State) :
    A.pool lim (M.stepEvents (rustDeallocEvents sz2 al2)
      (M.stepEvents (rustDeallocEvents sz1 al1) st)) s1 ⊢
      ∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1 := by
  rw [← M.stepEvents_append (rustDeallocEvents sz1 al1) (rustDeallocEvents sz2 al2) st]
  exact Entails.sepExists_right (rustDeallocEvents sz1 al1 ++ rustDeallocEvents sz2 al2)
    (Entails.pure_right
      (FreeOnlyEvs.append (FreeOnlyEvs.singleton al1 sz1) (FreeOnlyEvs.singleton al2 sz2))
      (Entails.refl _))

/-! ## Stage P4 `store_session` `Ok` Epilogue (`+0x048c → retAddr`) -/

set_option maxHeartbeats 1200000 in
private theorem p4_seg4e_prev1_c0_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr retPtr prevCap prevPtr p
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ 0#64) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1) ∗
          stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hlay_q : LayoutOk (prevCap.toNat * 24) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  obtain ⟨hlay_q1, hlay_q2, hlay_q3⟩ := hlay_q
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = retPtr := hx26
  dsimp only [dpClosureEntryP34Placed] at hpc
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  refine SepWP.weaken_pre
    (entails_replace_sub_p34_pl
      (prevVec1_outer_merge_p34_pl prevPtr 0#64 p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, st)
  wp_steps_sync_518 ext retAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [calleeSavedVRegs, wp_norm, arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]
  refine entails_replace_sub_p34_pl
    (pool_entails_freeOnly_one A lim st (prevCap.toNat * 24) 8 _)
    (by sep_focus) (by sep_focus)

set_option maxHeartbeats 1200000 in
private theorem p4_seg4e_prev1_cnz_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr retPtr prevCap prevPtr c p
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (hcap_nz : prevCap ≠ 0#64)
    (hcapb : 1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63)
    (hc_nz : c ≠ 0#64) (hc_lt : c.toNat < 2 ^ 63)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
       A.live prevPtr (prevCap.toNat * 24) 8 ∗
       (prevPtr ↦₆₄ c) ∗ ((prevPtr + 8#64) ↦₆₄ p) ∗
       memRegion (prevPtr + 16#64) 8 ∗
       A.live p c.toNat 1 ∗ memRegion p c.toNat ∗
       memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24) ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1) ∗
          stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp
  have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_nz
  have hc_beq : (c == 0#64) = false := beq_eq_false_iff_ne.mpr hc_nz
  have hc_pos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc_nz
    · exact hpos
  have hlay_c : LayoutOk c.toNat 1 := ⟨hc_pos, ⟨0, rfl⟩, by omega⟩
  obtain ⟨hlay_c1, hlay_c2, hlay_c3⟩ := hlay_c
  have hlay_q : LayoutOk (prevCap.toNat * 24) 8 := ⟨by omega, ⟨3, rfl⟩, by omega⟩
  obtain ⟨hlay_q1, hlay_q2, hlay_q3⟩ := hlay_q
  have hmul24' : (prevCap + (prevCap <<< 1)) <<< 3 = prevCap * 24#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  have hmul24 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = prevCap * 24#64 := hmul24'
  have hx1_de2 : (prevCap + (prevCap <<< 1#64)) <<< 3#64 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24]; bv_omega
  have hx1_de2' : (prevCap + (prevCap <<< 1)) <<< 3 = BitVec.ofNat 64 (prevCap.toNat * 24) := by
    rw [hmul24']; bv_omega
  have hx1_de2_nat : ((prevCap + (prevCap <<< 1#64)) <<< 3#64).toNat = prevCap.toNat * 24 := by
    rw [hmul24]; bv_omega
  have hx1_de2_nat' : ((prevCap + (prevCap <<< 1)) <<< 3).toNat = prevCap.toNat * 24 := by
    rw [hmul24']; bv_omega
  rw [hdrP_coro_eq]
  simp only [sepConj_assoc]
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptextHead.zeroExtend 64 := hx22
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = retPtr := hx26
  dsimp only [dpClosureEntryP34Placed] at hpc
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  wp_call hdealloc (p, c.toNat, 1, st)
  wp_steps_sync_518 ext (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
  refine SepWP.weaken_pre
    (entails_replace_sub_p34_pl
      (prevVec1_outer_merge_p34_pl prevPtr c p prevCap.toNat hcapb)
      (by sep_focus) rfl) ?_
  wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, M.stepEvents (rustDeallocEvents c.toNat 1) st)
  wp_steps_sync_518 ext retAddr
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, ProofLib.NonSyscallPreserved, AllocCallPreserved],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [calleeSavedVRegs, wp_norm, arm64_norm]⟩
  simp_all only [BitVec.add_zero, sepConj_assoc]
  refine entails_replace_sub_p34_pl
    (pool_entails_freeOnly_two A lim st c.toNat 1 (prevCap.toNat * 24) 8 _)
    (by sep_focus) (by sep_focus)

/-- Budget-threaded placed 1-element `previous_sessions` Stage P4 `Ok` epilogue (`+0x048c → retAddr`)
advancing `A.pool` along `FreeOnlyEvs`. -/
theorem p4_seg4e_prev1_of_dealloc_placed_wp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (st : M.σ) (s : State) (coroPtr retPtr prevCap prevPtr
      ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
      savedX25 savedX26 savedX27 savedX28 savedX29 retAddr : BitVec 64)
    (ptextHead w_390 u_ret08 u_ret2c : BitVec 32) (b_2c0 : BitVec 8)
    (enc : List (BitVec 8))
    (hpc : s.pc = dpClosureEntryP34Placed + 0x48c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx22 : s.readReg64 .x22 = ptextHead.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = retPtr) :
    SepWP (lsProg_518 ext) retAddr s
      (prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       A.pool lim st s ∗ stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((retPtr + 0x0#64) ↦₆₄ u_ret0) ∗ ((retPtr + 0x8#64) ↦₃₂ u_ret08) ∗
       ((retPtr + 0xc#64) ↦₆₄ u_ret0c) ∗ ((retPtr + 0x14#64) ↦₆₄ u_ret14) ∗
       ((retPtr + 0x1c#64) ↦₆₄ u_ret1c) ∗ ((retPtr + 0x24#64) ↦₆₄ u_ret24) ∗
       ((retPtr + 0x2c#64) ↦₃₂ u_ret2c) ∗
       ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
       ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
       ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
       ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
       ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
       ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
       ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
       ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19))
      (fun s1 P_f =>
        (P_f ⊢
          HdrP (coroPtr + 0xe0#64) prevCap prevPtr 1#64 ∗
          (∃∗ evs : List AllocEvent,
            ⌜FreeOnlyEvs evs⌝ ∗ A.pool lim (M.stepEvents evs st) s1) ∗
          stackAt s.sp allocHookStack ∗ ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((retPtr + 0x0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((retPtr + 0x8#64) ↦₃₂ ptextHead) ∗
          ((retPtr + 0xc#64) ↦₆₄ ptextMid0) ∗
          ((retPtr + 0x14#64) ↦₆₄ ptextMid1) ∗
          ((retPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((retPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((retPtr + 0x2c#64) ↦₃₂ w_390) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗ ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₆₄ w_380) ∗ ((s.sp + 0x388#64) ↦₆₄ w_388) ∗
          ((s.sp + 0x390#64) ↦₃₂ w_390) ∗
          ((s.sp + 0xc70#64) ↦₆₄ savedX29) ∗ ((s.sp + 0xc78#64) ↦₆₄ retAddr) ∗
          ((s.sp + 0xc80#64) ↦₆₄ savedX28) ∗ ((s.sp + 0xc88#64) ↦₆₄ savedX27) ∗
          ((s.sp + 0xc90#64) ↦₆₄ savedX26) ∗ ((s.sp + 0xc98#64) ↦₆₄ savedX25) ∗
          ((s.sp + 0xca0#64) ↦₆₄ savedX24) ∗ ((s.sp + 0xca8#64) ↦₆₄ savedX23) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ savedX22) ∗ ((s.sp + 0xcb8#64) ↦₆₄ savedX21) ∗
          ((s.sp + 0xcc0#64) ↦₆₄ savedX20) ∗ ((s.sp + 0xcc8#64) ↦₆₄ savedX19)) ∧
        s1.sp = s.sp + 0xcd0#64 ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = savedX19 ∧ s1.readReg64 .x20 = savedX20 ∧
        s1.readReg64 .x21 = savedX21 ∧ s1.readReg64 .x22 = savedX22 ∧
        s1.readReg64 .x23 = savedX23 ∧ s1.readReg64 .x24 = savedX24 ∧
        s1.readReg64 .x25 = savedX25 ∧ s1.readReg64 .x26 = savedX26 ∧
        s1.readReg64 .x27 = savedX27 ∧ s1.readReg64 .x28 = savedX28 ∧
        s1.readReg64 .x29 = savedX29 ∧ s1.readReg64 .x30 = retAddr ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  by_cases hcap : prevCap = 0#64
  · subst hcap
    refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_cap0_false_p34_pl A.repAlloc (coroPtr + 0xe0#64) prevPtr enc)) ?_
    exact sepWP_pure_elim_p34_pl fun h => False.elim h
  · refine SepWP.weaken_pre
      (sepConj_mono_left (prevVecAt_one_drop_split_p34_pl A.repAlloc (coroPtr + 0xe0#64) prevCap prevPtr enc hcap)) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    refine sepWP_exists_elim_p34_pl fun c => sepWP_exists_elim_p34_pl fun p => ?_
    refine sepWP_pure_elim_p34_pl fun ⟨hcap1, hcap2, _⟩ => ?_
    refine sepWP_pure_elim_p34_pl fun hc => ?_
    by_cases hc0 : c = 0#64
    · subst hc0
      conv => arg 4; simp only [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
      refine SepWP.weaken_pre ?_
        (p4_seg4e_prev1_c0_placed_wp ext hdealloc st
          s coroPtr retPtr prevCap prevPtr p
          ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          ptextHead w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hpc hrun hsp hx19 hx22 hx25 hx26)
      exact Entails.of_eq (by sep_ac_rfl)
    · conv => arg 4; simp only [hc0, ↓reduceIte, sepConj_assoc]
      refine SepWP.weaken_pre ?_
        (p4_seg4e_prev1_cnz_placed_wp ext hdealloc st
          s coroPtr retPtr prevCap prevPtr c p
          ptextMid0 ptextMid1 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
          savedX19 savedX20 savedX21 savedX22 savedX23 savedX24
          savedX25 savedX26 savedX27 savedX28 savedX29 retAddr
          ptextHead w_390 u_ret08 u_ret2c b_2c0
          hcap ⟨hcap1, hcap2⟩ hc0 hc hpc hrun hsp hx19 hx22 hx25 hx26)
      exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsBPlacedBudget
