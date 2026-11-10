/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib
public meta import ProofLib.Exec
public import ProofLib.SepLogic.CFG

/-!
# Step-Indexed CFG Combinator Tests

Unit proofs and concrete `execUntilPC` conformance checks for the `ProofLib.SepLogic.CFG`
combinators (`wp_if_join`, `SepWP.loop_measure_fuel`, `SepWP.loop_fuel`, `SepWP.loop_latch`,
`SepWP.loop_multi_exit`, `SepWP.nested_loop`, `SepWP.cfg_fixpoint`, and `SepWP.cfg_fixpoint_tree`).
-/

@[expose] public section

namespace Testing.CFGTest

open Arm64 ProofLib

set_option maxHeartbeats 400000
arm64_proof_prelude

/-! ## Diamond Join -/

@[simp, arm64_norm] def cfg_diamond_addr : BitVec 64 := 0x40000#64

def cfgDiamondCode : FnCode :=
  .atAddr "cfg_diamond" cfg_diamond_addr
    ("b4000060 " ++ -- 0x40000: cbz x0, 0x4000c
     "91005020 " ++ -- 0x40004: add x0, x1, #20
     "14000002 " ++ -- 0x40008: b 0x40010
     "91002820 " ++ -- 0x4000c: add x0, x1, #10
     "8b020000 " ++ -- 0x40010: add x0, x0, x2
     "f9000060 " ++ -- 0x40014: str x0, [x3]
     "d65f03c0")    -- 0x40018: ret

@[simp, arm64_norm]
def cfgDiamondJoinVal (cond x1 : BitVec 64) : BitVec 64 :=
  if cond = 0#64 then x1 + 10#64 else x1 + 20#64

@[simp, arm64_norm]
def cfgDiamondExpected (cond x1 x2 : BitVec 64) : BitVec 64 :=
  cfgDiamondJoinVal cond x1 + x2

structure CfgDiamondGhost where
  cond : BitVec 64
  x1   : BitVec 64
  x2   : BitVec 64
  ptr  : BitVec 64
  old  : BitVec 64

abbrev cfgDiamondSpec : Spec CfgDiamondGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.cond ∧
     s0.readReg64 .x1 = g.x1 ∧
     s0.readReg64 .x2 = g.x2 ∧
     s0.readReg64 .x3 = g.ptr⌝ ∗
    (g.ptr ↦₆₄ g.old)
  post := fun g _ sf =>
    ⌜sf.readReg64 .x0 = cfgDiamondExpected g.cond g.x1 g.x2⌝ ∗
    (g.ptr ↦₆₄ cfgDiamondExpected g.cond g.x1 g.x2)

theorem cfg_diamond_ok (prog : Program) (h_code : cfgDiamondCode.holds prog) :
    prog.subroutineOk "cfg_diamond" cfgDiamondSpec := by
  wp_init g s0
  wp_step
  wp_if_join 0x40010#64
    (fun sj =>
      sj.readReg64 .x0 = cfgDiamondJoinVal g.cond g.x1 ∧
      sj.readReg64 .x2 = g.x2 ∧
      sj.readReg64 .x3 = g.ptr ∧
      sj.readReg64 .lr = s0.readReg64 .lr ∧
      sj.sp = s0.sp ∧
      CalleeSavedPreserved s0 sj)
  ·
    wp_steps
    wp_done
  ·
    wp_steps
    wp_done
  ·
    intro sj hpc_j hrun_j ⟨hx0_j, hx2_j, hx3_j, hlr_j, hsp_j, hcs_j⟩
    wp_steps
    wp_done

/-! ## Single Loop -/

@[simp, arm64_norm] def cfg_loop_addr : BitVec 64 := 0x41000#64

def cfgLoopCode : FnCode :=
  .atAddr "cfg_loop" cfg_loop_addr
    ("b4000081 " ++ -- 0x41000: cbz x1, 0x41010
     "8b020000 " ++ -- 0x41004: add x0, x0, x2
     "d1000421 " ++ -- 0x41008: sub x1, x1, #1
     "17fffffd " ++ -- 0x4100c: b 0x41000
     "d65f03c0")    -- 0x41010: ret

abbrev cfgLoopInv (s0 : State) (acc step : BitVec 64) (m k : Nat) (st : State) : Prop :=
  k ≤ m ∧
  st.readReg64 .x0 = acc + BitVec.ofNat 64 (m - k) * step ∧
  st.readReg64 .x1 = BitVec.ofNat 64 k ∧
  st.readReg64 .x2 = step ∧
  st.readReg64 .lr = s0.readReg64 .lr ∧
  st.sp = s0.sp ∧
  CalleeSavedPreserved s0 st

theorem cfg_loop_measure_fuel_ok (prog : Program) (h_code : cfgLoopCode.holds prog)
    (s0 : State) (acc step : BitVec 64) (m fuel : Nat) (P : SepProp)
    (hm_lt : m < 2 ^ 64)
    (hbud : 4 * m + 2 ≤ fuel)
    (hpc : s0.pc = 0x41000#64)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx2 : s0.readReg64 .x2 = step) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = acc + BitVec.ofNat 64 m * step ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  refine SepWP.loop_measure_fuel 4 2
    (fun _ _ => P) (cfgLoopInv s0 acc step m)
    hbud hpc hrun (Entails.refl P)
    ⟨Nat.le_refl m, by simp [hx0], hx1, hx2, rfl, rfl, CalleeSavedPreserved.rfl s0⟩
    ?_ ?_
  ·
    intro f st _ hpc_st hrun_st ⟨_, hx0_st, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    simp only [Nat.sub_zero] at hx0_st
    wp_steps
    wp_done
  ·
    intro k' f st _ hpc_st hrun_st ⟨hk_le, hx0_st, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    right
    have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
    have hk_sub : BitVec.ofNat 64 (k' + 1) - 1#64 = BitVec.ofNat 64 k' := by bv_omega
    have hacc_step :
        acc + BitVec.ofNat 64 (m - (k' + 1)) * step + step =
          acc + BitVec.ofNat 64 (m - k') * step := by
      have hm_eq : m - k' = (m - (k' + 1)) + 1 := by omega
      rw [hm_eq, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul, BitVec.add_assoc]
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx2_st]
    · simp [wp_norm, arm64_norm, hlr_st]
    · simp [wp_norm, arm64_norm, hsp_st]
    · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

theorem cfg_loop_fuel_ok (prog : Program) (h_code : cfgLoopCode.holds prog)
    (s0 : State) (acc step : BitVec 64) (m : Nat) (P : SepProp)
    (hm_lt : m < 2 ^ 64)
    (hpc : s0.pc = 0x41000#64)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx2 : s0.readReg64 .x2 = step) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = acc + BitVec.ofNat 64 m * step ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  refine SepWP.loop_fuel (cfgLoopInv s0 acc step m) hpc hrun
    ⟨Nat.le_refl m, by simp [hx0], hx1, hx2, rfl, rfl, CalleeSavedPreserved.rfl s0⟩ ?_
  intro k st hpc_st hrun_st ⟨hk_le, hx0_st, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
  cases k with
  | zero =>
    left
    simp only [Nat.sub_zero] at hx0_st
    wp_steps
    wp_done
  | succ k' =>
    right
    refine ⟨1, by omega, by omega, ?_⟩
    simp only [Nat.add_sub_cancel]
    have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
    have hk_sub : BitVec.ofNat 64 (k' + 1) - 1#64 = BitVec.ofNat 64 k' := by bv_omega
    have hacc_step :
        acc + BitVec.ofNat 64 (m - (k' + 1)) * step + step =
          acc + BitVec.ofNat 64 (m - k') * step := by
      have hm_eq : m - k' = (m - (k' + 1)) + 1 := by omega
      rw [hm_eq, BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul, BitVec.add_assoc]
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx2_st]
    · simp [wp_norm, arm64_norm, hlr_st]
    · simp [wp_norm, arm64_norm, hsp_st]
    · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

/-! ## Multi-Exit and Header-Latch Loops -/

@[simp, arm64_norm] def cfg_multi_exit_addr : BitVec 64 := 0x42000#64

def cfgMultiExitCode : FnCode :=
  .atAddr "cfg_multi_exit" cfg_multi_exit_addr
    ("eb02001f " ++ -- 0x42000: cmp x0, x2
     "540000c0 " ++ -- 0x42004: b.eq 0x4201c
     "b4000081 " ++ -- 0x42008: cbz x1, 0x42018
     "91000400 " ++ -- 0x4200c: add x0, x0, #1
     "d1000421 " ++ -- 0x42010: sub x1, x1, #1
     "17fffffb " ++ -- 0x42014: b 0x42000
     "92800000 " ++ -- 0x42018: movn x0, #0
     "d65f03c0")    -- 0x4201c: ret

def cfgMultiExitRef : Nat → BitVec 64 → BitVec 64 → BitVec 64
  | 0, idx, target =>
    if idx == target then idx else 0xffffffffffffffff#64
  | k + 1, idx, target =>
    if idx == target then idx else cfgMultiExitRef k (idx + 1#64) target

theorem cfg_multi_exit_latch_ok (prog : Program) (h_code : cfgMultiExitCode.holds prog)
    (s0 : State) (idx0 target : BitVec 64) (m : Nat) (P : SepProp)
    (hm_lt : m < 2 ^ 64)
    (hpc : s0.pc = 0x42000#64)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = idx0)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx2 : s0.readReg64 .x2 = target) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = cfgMultiExitRef m idx0 target ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  let Inv_head : Nat → State → Prop := fun k st =>
    k ≤ m ∧
    cfgMultiExitRef k (st.readReg64 .x0) target = cfgMultiExitRef m idx0 target ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = target ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  let Inv_latch : Nat → State → Prop := fun k st =>
    k ≤ m ∧
    st.readReg64 .x0 ≠ target ∧
    cfgMultiExitRef k (st.readReg64 .x0) target = cfgMultiExitRef m idx0 target ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = target ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  refine SepWP.loop_latch (head_pc := 0x42000#64) (latch_pc := 0x42008#64)
    (fun _ _ => P) (fun _ _ => P) Inv_head Inv_latch
    hpc hrun (Entails.refl P)
    ⟨Nat.le_refl m, by rw [hx0], hx1, hx2, rfl, rfl, CalleeSavedPreserved.rfl s0⟩
    ?_ ?_ ?_
  ·
    intro k st hpc_st hrun_st ⟨hk_le, href, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    by_cases hhit : st.readReg64 .x0 = target
    ·
      left
      have href_hit : cfgMultiExitRef k (st.readReg64 .x0) target = st.readReg64 .x0 := by
        cases k <;> simp [cfgMultiExitRef, hhit]
      wp_steps
      wp_done
    ·
      right
      have hhit_beq : (st.readReg64 (.gpr 0#5) == target) = false :=
        beq_eq_false_iff_ne.mpr hhit
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨⟨hk_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
      · simp [wp_norm, arm64_norm, hhit]
      · simp [wp_norm, arm64_norm, href]
      · simp [wp_norm, arm64_norm, hx1_st]
      · simp [wp_norm, arm64_norm, hx2_st]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])
  ·
    intro st hpc_st hrun_st ⟨_, hmiss, href, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    have href0 : cfgMultiExitRef 0 (st.readReg64 .x0) target = 0xffffffffffffffff#64 := by
      simp [cfgMultiExitRef, hmiss]
    wp_steps
    wp_done
  ·
    intro k' st hpc_st hrun_st ⟨hk_le, hmiss, href, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
    have hk_sub : BitVec.ofNat 64 (k' + 1) - 1#64 = BitVec.ofNat 64 k' := by bv_omega
    have href_step : cfgMultiExitRef k' (st.readReg64 .x0 + 1#64) target = cfgMultiExitRef m idx0 target := by
      rw [← href]
      simp [cfgMultiExitRef, hmiss]
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm, href_step]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx2_st]
    · simp [wp_norm, arm64_norm, hlr_st]
    · simp [wp_norm, arm64_norm, hsp_st]
    · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

theorem cfg_multi_exit_single_cut_ok (prog : Program) (h_code : cfgMultiExitCode.holds prog)
    (s0 : State) (idx0 target : BitVec 64) (m : Nat) (P : SepProp)
    (hm_lt : m < 2 ^ 64)
    (hpc : s0.pc = 0x42000#64)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = idx0)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 m)
    (hx2 : s0.readReg64 .x2 = target) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = cfgMultiExitRef m idx0 target ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  let Inv : Nat → State → Prop := fun k st =>
    k ≤ m ∧
    cfgMultiExitRef k (st.readReg64 .x0) target = cfgMultiExitRef m idx0 target ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x2 = target ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  refine SepWP.loop_multi_exit (fun _ _ => P) Inv hpc hrun (Entails.refl P)
    ⟨Nat.le_refl m, by rw [hx0], hx1, hx2, rfl, rfl, CalleeSavedPreserved.rfl s0⟩ ?_ ?_
  ·
    intro st hpc_st hrun_st ⟨_, href, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    by_cases hhit : st.readReg64 .x0 = target
    · have href_hit : cfgMultiExitRef 0 (st.readReg64 .x0) target = st.readReg64 .x0 := by
        simp [cfgMultiExitRef, hhit]
      wp_steps
      wp_done
    · have hhit_beq : (st.readReg64 (.gpr 0#5) == target) = false :=
        beq_eq_false_iff_ne.mpr hhit
      have href0 : cfgMultiExitRef 0 (st.readReg64 .x0) target = 0xffffffffffffffff#64 := by
        simp [cfgMultiExitRef, hhit]
      wp_steps
      wp_done
  ·
    intro k' st hpc_st hrun_st ⟨hk_le, href, hx1_st, hx2_st, hlr_st, hsp_st, hcs_st⟩
    by_cases hhit : st.readReg64 .x0 = target
    · left
      have href_hit : cfgMultiExitRef (k' + 1) (st.readReg64 .x0) target = st.readReg64 .x0 := by
        simp [cfgMultiExitRef, hhit]
      wp_steps
      wp_done
    · right
      have hhit_beq : (st.readReg64 (.gpr 0#5) == target) = false :=
        beq_eq_false_iff_ne.mpr hhit
      have hk_nz : BitVec.ofNat 64 (k' + 1) ≠ 0#64 := by bv_omega
      have hk_sub : BitVec.ofNat 64 (k' + 1) - 1#64 = BitVec.ofNat 64 k' := by bv_omega
      have href_step : cfgMultiExitRef k' (st.readReg64 .x0 + 1#64) target = cfgMultiExitRef m idx0 target := by
        rw [← href]
        simp [cfgMultiExitRef, hhit]
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
      · simp [wp_norm, arm64_norm, href_step]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hx2_st]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

/-! ## Nested Loops -/

@[simp, arm64_norm] def cfg_nested_addr : BitVec 64 := 0x43000#64

def cfgNestedLoopCode : FnCode :=
  .atAddr "cfg_nested_loop" cfg_nested_addr
    ("b4000101 " ++ -- 0x43000: cbz x1, 0x43020
     "91000062 " ++ -- 0x43004: add x2, x3, #0
     "b4000082 " ++ -- 0x43008: cbz x2, 0x43018
     "91000400 " ++ -- 0x4300c: add x0, x0, #1
     "d1000442 " ++ -- 0x43010: sub x2, x2, #1
     "17fffffd " ++ -- 0x43014: b 0x43008
     "d1000421 " ++ -- 0x43018: sub x1, x1, #1
     "17fffff9 " ++ -- 0x4301c: b 0x43000
     "d65f03c0")    -- 0x43020: ret

theorem cfg_nested_inner_ok (prog : Program) (h_code : cfgNestedLoopCode.holds prog)
    (s0 st : State) (baseAcc : BitVec 64) (x1Val : BitVec 64) (innerLen : Nat) (P : SepProp)
    (hin_lt : innerLen < 2 ^ 64)
    (hpc : st.pc = 0x43008#64)
    (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = baseAcc)
    (hx1 : st.readReg64 .x1 = x1Val)
    (hx2 : st.readReg64 .x2 = BitVec.ofNat 64 innerLen)
    (hx3 : st.readReg64 .x3 = BitVec.ofNat 64 innerLen)
    (hlr : st.readReg64 .lr = s0.readReg64 .lr)
    (hsp : st.sp = s0.sp)
    (hcs : CalleeSavedPreserved s0 st) :
    SepWP prog 0x43018#64 st P
      (sepPost (fun se =>
        se.readReg64 .x0 = baseAcc + BitVec.ofNat 64 innerLen ∧
        se.readReg64 .x1 = x1Val ∧
        se.readReg64 .x3 = BitVec.ofNat 64 innerLen ∧
        se.readReg64 .lr = s0.readReg64 .lr ∧
        se.sp = s0.sp ∧
        CalleeSavedPreserved s0 se) P) := by
  let InvIn : Nat → State → Prop := fun j si =>
    j ≤ innerLen ∧
    si.readReg64 .x0 = baseAcc + BitVec.ofNat 64 (innerLen - j) ∧
    si.readReg64 .x1 = x1Val ∧
    si.readReg64 .x2 = BitVec.ofNat 64 j ∧
    si.readReg64 .x3 = BitVec.ofNat 64 innerLen ∧
    si.readReg64 .lr = s0.readReg64 .lr ∧
    si.sp = s0.sp ∧
    CalleeSavedPreserved s0 si
  refine SepWP.loop_measure InvIn hpc hrun
    ⟨Nat.le_refl innerLen, by simp [hx0], hx1, hx2, hx3, hlr, hsp, hcs⟩ ?_ ?_
  · intro si hpc_i hrun_i ⟨_, hx0_i, hx1_i, hx2_i, hx3_i, hlr_i, hsp_i, hcs_i⟩
    wp_steps
    wp_done
  · intro j' si hpc_i hrun_i ⟨hj_le, hx0_i, hx1_i, hx2_i, hx3_i, hlr_i, hsp_i, hcs_i⟩
    right
    have hj_nz : BitVec.ofNat 64 (j' + 1) ≠ 0#64 := by bv_omega
    have hj_sub : BitVec.ofNat 64 (j' + 1) - 1#64 = BitVec.ofNat 64 j' := by bv_omega
    have hacc_step :
        baseAcc + BitVec.ofNat 64 (innerLen - (j' + 1)) + 1#64 =
          baseAcc + BitVec.ofNat 64 (innerLen - j') := by
      have heq : innerLen - j' = (innerLen - (j' + 1)) + 1 := by omega
      rw [heq, BitVec.ofNat_add, BitVec.add_assoc]
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_i]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx1_i]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx3_i]
    · simp [wp_norm, arm64_norm, hlr_i]
    · simp [wp_norm, arm64_norm, hsp_i]
    · exact hcs_i.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

theorem cfg_nested_loop_ok (prog : Program) (h_code : cfgNestedLoopCode.holds prog)
    (s0 : State) (acc : BitVec 64) (outerLen innerLen : Nat) (P : SepProp)
    (hout_lt : outerLen < 2 ^ 64)
    (hin_lt : innerLen < 2 ^ 64)
    (hpc : s0.pc = 0x43000#64)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 outerLen)
    (hx3 : s0.readReg64 .x3 = BitVec.ofNat 64 innerLen) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = acc + BitVec.ofNat 64 (outerLen * innerLen) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  let Inv_outer : Nat → State → Prop := fun k st =>
    k ≤ outerLen ∧
    st.readReg64 .x0 = acc + BitVec.ofNat 64 ((outerLen - k) * innerLen) ∧
    st.readReg64 .x1 = BitVec.ofNat 64 k ∧
    st.readReg64 .x3 = BitVec.ofNat 64 innerLen ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  let Inv_inner : Nat → State → Prop := fun k st =>
    k < outerLen ∧
    st.readReg64 .x0 = acc + BitVec.ofNat 64 ((outerLen - (k + 1)) * innerLen) ∧
    st.readReg64 .x1 = BitVec.ofNat 64 (k + 1) ∧
    st.readReg64 .x2 = BitVec.ofNat 64 innerLen ∧
    st.readReg64 .x3 = BitVec.ofNat 64 innerLen ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  let Inv_inner_exit : Nat → State → Prop := fun k st =>
    k < outerLen ∧
    st.readReg64 .x0 = acc + BitVec.ofNat 64 ((outerLen - k) * innerLen) ∧
    st.readReg64 .x1 = BitVec.ofNat 64 (k + 1) ∧
    st.readReg64 .x3 = BitVec.ofNat 64 innerLen ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  refine SepWP.nested_loop
    (outer_pc := 0x43000#64) (inner_pc := 0x43008#64) (inner_exit_pc := 0x43018#64)
    (fun _ _ => P) (fun _ _ => P) (fun _ _ => P)
    Inv_outer Inv_inner Inv_inner_exit
    hpc hrun (Entails.refl P)
    ⟨Nat.le_refl outerLen, by simp [hx0], hx1, hx3, rfl, rfl, CalleeSavedPreserved.rfl s0⟩
    ?_ ?_ ?_ ?_
  ·
    intro st hpc_st hrun_st ⟨_, hx0_st, hx1_st, hx3_st, hlr_st, hsp_st, hcs_st⟩
    simp only [Nat.sub_zero] at hx0_st
    wp_steps
    wp_done
  ·
    intro k st hpc_st hrun_st ⟨hk_le, hx0_st, hx1_st, hx3_st, hlr_st, hsp_st, hcs_st⟩
    right; right
    have hk_nz : BitVec.ofNat 64 (k + 1) ≠ 0#64 := by bv_omega
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm, hx0_st]
    · simp [wp_norm, arm64_norm, hx1_st]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx3_st]
    · simp [wp_norm, arm64_norm, hlr_st]
    · simp [wp_norm, arm64_norm, hsp_st]
    · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])
  ·
    intro k st hpc_st hrun_st ⟨hk_lt, hx0_st, hx1_st, hx2_st, hx3_st, hlr_st, hsp_st, hcs_st⟩
    have hinner := cfg_nested_inner_ok prog h_code s0 st
      (acc + BitVec.ofNat 64 ((outerLen - (k + 1)) * innerLen))
      (BitVec.ofNat 64 (k + 1)) innerLen P hin_lt
      hpc_st hrun_st hx0_st hx1_st hx2_st hx3_st hlr_st hsp_st hcs_st
    refine SepWP.mono hinner ?_
    intro se Pe _ _ ⟨⟨hx0_e, hx1_e, hx3_e, hlr_e, hsp_e, hcs_e⟩, hent_e⟩
    have hacc_mul :
        acc + BitVec.ofNat 64 ((outerLen - (k + 1)) * innerLen) + BitVec.ofNat 64 innerLen =
          acc + BitVec.ofNat 64 ((outerLen - k) * innerLen) := by
      have hsub : outerLen - k = (outerLen - (k + 1)) + 1 := by omega
      rw [hsub, Nat.succ_mul, BitVec.ofNat_add, BitVec.add_assoc]
    exact ⟨⟨hk_lt, hx0_e.trans hacc_mul, hx1_e, hx3_e, hlr_e, hsp_e, hcs_e⟩, hent_e⟩
  ·
    intro k st hpc_st hrun_st ⟨hk_lt, hx0_st, hx1_st, hx3_st, hlr_st, hsp_st, hcs_st⟩
    have hk_sub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by bv_omega
    wp_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
    refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
    · simp [wp_norm, arm64_norm, hx0_st]
    · simp [wp_norm, arm64_norm]
    · simp [wp_norm, arm64_norm, hx3_st]
    · simp [wp_norm, arm64_norm, hlr_st]
    · simp [wp_norm, arm64_norm, hsp_st]
    · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

/-! ## Mutual Multi-Label State Machine -/

@[simp, arm64_norm] def cfg_sm_addr : BitVec 64 := 0x44000#64

def cfgStateMachineCode : FnCode :=
  .atAddr "cfg_state_machine" cfg_sm_addr
    ("b40000e1 " ++ -- 0x44000: cbz x1, 0x4401c
     "91000800 " ++ -- 0x44004: add x0, x0, #2
     "d1000421 " ++ -- 0x44008: sub x1, x1, #1
     "b4000081 " ++ -- 0x4400c: cbz x1, 0x4401c
     "91000c00 " ++ -- 0x44010: add x0, x0, #3
     "d1000421 " ++ -- 0x44014: sub x1, x1, #1
     "17fffffa " ++ -- 0x44018: b 0x44000
     "d65f03c0")    -- 0x4401c: ret

inductive ModeLabel where
  | modeA
  | modeB

@[simp, arm64_norm]
def modeCutPC : ModeLabel → BitVec 64
  | .modeA => 0x44000#64
  | .modeB => 0x4400c#64

@[simp]
def smGain : ModeLabel → Nat → Nat
  | _, 0 => 0
  | .modeA, f + 1 => 2 + smGain .modeB f
  | .modeB, f + 1 => 3 + smGain .modeA f

theorem cfg_state_machine_ok (prog : Program) (h_code : cfgStateMachineCode.holds prog)
    (s0 : State) (l0 : ModeLabel) (acc : BitVec 64) (fuel : Nat) (P : SepProp)
    (hfuel_lt : fuel < 2 ^ 64)
    (hpc : s0.pc = modeCutPC l0)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 fuel) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = acc + BitVec.ofNat 64 (smGain l0 fuel) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  let Inv : ModeLabel → State → Nat → Prop := fun l st f =>
    f ≤ fuel ∧
    st.readReg64 .x0 + BitVec.ofNat 64 (smGain l f) = acc + BitVec.ofNat 64 (smGain l0 fuel) ∧
    st.readReg64 .x1 = BitVec.ofNat 64 f ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  refine SepWP.cfg_fixpoint modeCutPC Inv ?_ hpc hrun
    ⟨Nat.le_refl fuel, by rw [hx0], hx1, rfl, rfl, CalleeSavedPreserved.rfl s0⟩
  intro l st f hpc_st hrun_st ⟨hf_le, hgain, hx1_st, hlr_st, hsp_st, hcs_st⟩
  cases f with
  | zero =>
    left
    have hx0_done : st.readReg64 .x0 = acc + BitVec.ofNat 64 (smGain l0 fuel) := by
      simpa using hgain
    cases l <;> simp only [modeCutPC] at hpc_st <;> {
      wp_steps
      wp_done
    }
  | succ f' =>
    right
    have hf_nz : BitVec.ofNat 64 (f' + 1) ≠ 0#64 := by bv_omega
    have hf_sub : BitVec.ofNat 64 (f' + 1) - 1#64 = BitVec.ofNat 64 f' := by bv_omega
    cases l with
    | modeA =>
      refine ⟨.modeB, 1, by omega, by omega, ?_⟩
      simp only [modeCutPC, Nat.add_sub_cancel] at hpc_st ⊢
      have hgain_step :
          st.readReg64 .x0 + 2#64 + BitVec.ofNat 64 (smGain .modeB f') =
            acc + BitVec.ofNat 64 (smGain l0 fuel) := by
        rw [← hgain, smGain, BitVec.ofNat_add, ← BitVec.add_assoc]
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
      · simp [wp_norm, arm64_norm, hgain_step]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])
    | modeB =>
      refine ⟨.modeA, 1, by omega, by omega, ?_⟩
      simp only [modeCutPC, Nat.add_sub_cancel] at hpc_st ⊢
      have hgain_step :
          st.readReg64 .x0 + 3#64 + BitVec.ofNat 64 (smGain .modeA f') =
            acc + BitVec.ofNat 64 (smGain l0 fuel) := by
        rw [← hgain, smGain, BitVec.ofNat_add, ← BitVec.add_assoc]
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_⟩, Entails.refl P⟩
      · simp [wp_norm, arm64_norm, hgain_step]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

theorem cfg_state_machine_tree_ok (prog : Program) (h_code : cfgStateMachineCode.holds prog)
    (s0 : State) (l0 : ModeLabel) (acc : BitVec 64) (fuel : Nat) (P : SepProp)
    (hfuel_lt : fuel < 2 ^ 64)
    (hpc : s0.pc = modeCutPC l0)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = acc)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 fuel) :
    SepWP prog (s0.readReg64 .lr) s0 P
      (sepPost (fun sf =>
        sf.readReg64 .x0 = acc + BitVec.ofNat 64 (smGain l0 fuel) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf) P) := by
  let Inv : ModeLabel → State → Nat → Prop := fun l st f =>
    f ≤ fuel ∧
    st.readReg64 .x0 + BitVec.ofNat 64 (smGain l f) = acc + BitVec.ofNat 64 (smGain l0 fuel) ∧
    st.readReg64 .x1 = BitVec.ofNat 64 f ∧
    st.readReg64 .lr = s0.readReg64 .lr ∧
    st.sp = s0.sp ∧
    CalleeSavedPreserved s0 st
  refine SepWP.cfg_fixpoint_tree modeCutPC (fun _ _ _ => P) Inv ?_ hpc hrun (Entails.refl P)
    ⟨Nat.le_refl fuel, by rw [hx0], hx1, rfl, rfl, CalleeSavedPreserved.rfl s0⟩
  intro l st f hpc_st hrun_st ⟨hf_le, hgain, hx1_st, hlr_st, hsp_st, hcs_st⟩
  cases f with
  | zero =>
    apply SepWP.CFGStep.exit
    have hx0_done : st.readReg64 .x0 = acc + BitVec.ofNat 64 (smGain l0 fuel) := by
      simpa using hgain
    cases l <;> simp only [modeCutPC] at hpc_st <;> {
      wp_steps
      wp_done
    }
  | succ f' =>
    have hf_nz : BitVec.ofNat 64 (f' + 1) ≠ 0#64 := by bv_omega
    have hf_sub : BitVec.ofNat 64 (f' + 1) - 1#64 = BitVec.ofNat 64 f' := by bv_omega
    cases l with
    | modeA =>
      refine SepWP.CFGStep.jump .modeB 1 (by omega) (by omega) ?_
      simp only [modeCutPC, Nat.add_sub_cancel] at hpc_st ⊢
      have hgain_step :
          st.readReg64 .x0 + 2#64 + BitVec.ofNat 64 (smGain .modeB f') =
            acc + BitVec.ofNat 64 (smGain l0 fuel) := by
        rw [← hgain, smGain, BitVec.ofNat_add, ← BitVec.add_assoc]
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨Entails.refl P, ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [wp_norm, arm64_norm, hgain_step]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])
    | modeB =>
      refine SepWP.CFGStep.jump .modeA 1 (by omega) (by omega) ?_
      simp only [modeCutPC, Nat.add_sub_cancel] at hpc_st ⊢
      have hgain_step :
          st.readReg64 .x0 + 3#64 + BitVec.ofNat 64 (smGain .modeA f') =
            acc + BitVec.ofNat 64 (smGain l0 fuel) := by
        rw [← hgain, smGain, BitVec.ofNat_add, ← BitVec.add_assoc]
      wp_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_st]) ?_
      refine ⟨Entails.refl P, ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [wp_norm, arm64_norm, hgain_step]
      · simp [wp_norm, arm64_norm]
      · simp [wp_norm, arm64_norm, hlr_st]
      · simp [wp_norm, arm64_norm, hsp_st]
      · exact hcs_st.trans (by simp (config := { decide := true }) [CalleeSavedPreserved, wp_norm, arm64_norm])

/-! ## Runtime Conformance Checks -/

def cfgTestRuntimeCheck : Bool :=
  let prog1 := Program.ofWords cfg_diamond_addr cfgDiamondCode.hex
  let s1_zero : State :=
    ({} : State).setMem (prog1.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 0#64 |>.writeReg64 .x1 100#64 |>.writeReg64 .x2 5#64
      |>.writeReg64 .x3 0x90000#64 |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_diamond_addr
  let sf1_zero := execUntilPC 20 prog1 0xdead0000#64 s1_zero
  let s1_nz : State :=
    ({} : State).setMem (prog1.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 1#64 |>.writeReg64 .x1 100#64 |>.writeReg64 .x2 5#64
      |>.writeReg64 .x3 0x90000#64 |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_diamond_addr
  let sf1_nz := execUntilPC 20 prog1 0xdead0000#64 s1_nz
  let prog2 := Program.ofWords cfg_loop_addr cfgLoopCode.hex
  let s2 : State :=
    ({} : State).setMem (prog2.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 10#64 |>.writeReg64 .x1 6#64 |>.writeReg64 .x2 7#64
      |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_loop_addr
  let sf2 := execUntilPC 50 prog2 0xdead0000#64 s2
  let prog3 := Program.ofWords cfg_multi_exit_addr cfgMultiExitCode.hex
  let s3_hit : State :=
    ({} : State).setMem (prog3.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 10#64 |>.writeReg64 .x1 5#64 |>.writeReg64 .x2 13#64
      |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_multi_exit_addr
  let sf3_hit := execUntilPC 50 prog3 0xdead0000#64 s3_hit
  let s3_miss : State :=
    ({} : State).setMem (prog3.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 10#64 |>.writeReg64 .x1 2#64 |>.writeReg64 .x2 15#64
      |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_multi_exit_addr
  let sf3_miss := execUntilPC 50 prog3 0xdead0000#64 s3_miss
  let prog4 := Program.ofWords cfg_nested_addr cfgNestedLoopCode.hex
  let s4 : State :=
    ({} : State).setMem (prog4.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 100#64 |>.writeReg64 .x1 4#64 |>.writeReg64 .x3 3#64
      |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_nested_addr
  let sf4 := execUntilPC 100 prog4 0xdead0000#64 s4
  let prog5 := Program.ofWords cfg_sm_addr cfgStateMachineCode.hex
  let s5 : State :=
    ({} : State).setMem (prog5.loadCode ({} : State).mem).mapRestRw
      |>.writeReg64 .x0 10#64 |>.writeReg64 .x1 5#64
      |>.writeReg64 .lr 0xdead0000#64 |>.setPC cfg_sm_addr
  let sf5 := execUntilPC 50 prog5 0xdead0000#64 s5
  sf1_zero.readReg64 .x0 == 115#64 &&
  sf1_zero.mem.read64 0x90000#64 == 115#64 &&
  sf1_nz.readReg64 .x0 == 125#64 &&
  sf1_nz.mem.read64 0x90000#64 == 125#64 &&
  sf2.readReg64 .x0 == 52#64 &&
  sf3_hit.readReg64 .x0 == 13#64 &&
  sf3_miss.readReg64 .x0 == 0xffffffffffffffff#64 &&
  sf4.readReg64 .x0 == 112#64 &&
  sf5.readReg64 .x0 == 22#64

#guard cfgTestRuntimeCheck

end Testing.CFGTest
