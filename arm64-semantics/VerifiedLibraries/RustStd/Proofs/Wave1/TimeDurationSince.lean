/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
public import VerifiedLibraries.RustStd.Proofs.Wave1.TimeDurationSinceLemmas

/-!
# Placement-Generic Proofs for `SystemTime::duration_since`

Proves `timeDurationSince_subroutineOk`, establishing `MultiPlacedLib.subroutineOk` for
`std::time::SystemTime::duration_since` (`timeMultiLib`) against `timeDurationSinceSpec`, via
`Timespec::sub_timespec` (`subTimespec_ge_block_ok` and `subTimespec_block_ok`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace VerifiedLibraries.RustStd

open Arm64 Arm64.Obj ProofLib

section
arm64_proof_prelude

private theorem entails_subst_frame {A B : SepProp} (F : SepProp) {P Q : SepProp}
    (hab : A ⊢ B) (h1 : P ⊢ A ∗ F) (h2 : B ∗ F ⊢ Q) : P ⊢ Q :=
  Arm64.Entails.trans h1 (Arm64.Entails.trans (sepConj_mono_left hab) h2)

/-! ## Internal Contracts for `Timespec::sub_timespec` -/

/-- Internal contract for `Timespec::sub_timespec` on the `t2 ≤ t1` (`Ok`) path (`64` B stack,
    `.rodata.cst16` unused). -/
def subTimespecGeSpec :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × BitVec 32 ×
      BitVec 64 × BitVec 64 × BitVec 32) where
  pre := fun (out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2) s0 =>
    ⌜s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = p1 ∧ s0.readReg64 .x2 = p2 ∧
      n1.toNat < 10 ^ 9 ∧ n2.toNat < 10 ^ 9 ∧ timespecNs s2 n2 ≤ timespecNs s1 n1⌝ ∗
    ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗
      (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
      stackAt s0.sp 64 ∗
      (out ↦₆₄ ow0) ∗ ((out + 8#64) ↦₆₄ ow1) ∗ ((out + 16#64) ↦₃₂ ow2))
  post := fun (out, p1, p2, s1, n1, s2, n2, _, _, _) s0 sf =>
    let d := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
    ⌜IoFrame s0 sf ∧ sf.fs = s0.fs⌝ ∗
    ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗
      (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
      stackAt s0.sp 64 ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((out + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Internal contract for `Timespec::sub_timespec` across both `t2 ≤ t1` (`Ok`) and `t1 < t2` (`Err`)
    paths (`128` B stack, `.rodata.cst16` at `c16`). -/
def subTimespecInternalSpec (c16 : BitVec 64) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × BitVec 32 ×
      BitVec 64 × BitVec 64 × BitVec 32) where
  pre := fun (out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2) s0 =>
    ⌜s0.readReg64 .x0 = out ∧ s0.readReg64 .x1 = p1 ∧ s0.readReg64 .x2 = p2 ∧
      n1.toNat < 10 ^ 9 ∧ n2.toNat < 10 ^ 9⌝ ∗
    ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗
      (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
      (c16 ↦ᵣ timePlacedData0) ∗
      stackAt s0.sp 128 ∗
      (out ↦₆₄ ow0) ∗ ((out + 8#64) ↦₆₄ ow1) ∗ ((out + 16#64) ↦₃₂ ow2))
  post := fun (out, p1, p2, s1, n1, s2, n2, _, _, _) s0 sf =>
    let t1 := timespecNs s1 n1
    let t2 := timespecNs s2 n2
    let d := (t1 - t2).natAbs
    ⌜IoFrame s0 sf ∧ sf.fs = s0.fs⌝ ∗
    ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗
      (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
      (c16 ↦ᵣ timePlacedData0) ∗
      stackAt s0.sp 128 ∗
      (out ↦₆₄ (if t2 ≤ t1 then 0#64 else 1#64)) ∗
      ((out + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((out + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-! ## `Timespec::sub_timespec` on the `t2 ≤ t1` Path -/

set_option maxHeartbeats 800000 in
theorem subTimespec_ge_block_ok [TimePlacement]
    (externs : String → Option (State → State) := fun _ => none) :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 0 externs)
      (timeMultiLib.fnAddr timeMpl timeSubTimespecLocalSym)
      subTimespecGeSpec := by
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2⟩ R s0 hpc hrun hpre _hsp
  dsimp only [subTimespecGeSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn1, hn2, hle⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  change SepWP (timePC00.rebase timePl00.base externs) (s0.readReg64 .lr) s0 _ _ _
  have hpc0 : s0.pc = timePl00.base := hpc; clear hpc; rename_i hpc
  have htbz : ((subTimespecCmpWord s1 s2 n1 n2).getLsbD 0 == false) = false :=
    subTimespec_tbz_eq_false_of_le hn1 hn2 hle
  dsimp only [subTimespecCmpWord] at htbz
  have hblo : (subTimespecNsec n1 n2).ult 1000000000#32 = true :=
    subTimespec_nsec_ult_e9 hn1 hn2
  dsimp only [subTimespecNsec] at hblo
  wp_conv_pre =>
    rw [stackAt_eq_cells s0.sp 8]
    simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, ProofLib.cells_sub_succ,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
    SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 => ?_
  wp_sym_steps
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨?_, by simp [wp_norm, arm64_norm],
    by simp [CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm]⟩
  intro hm_f
  refine Satisfies.mono ?_ hm_f
  have hsec := subTimespec_secs_eq_div hn1 hn2 hle
  have hnsec := subTimespec_nsec_eq_mod hn1 hn2 hle
  dsimp only [subTimespecSecs] at hsec
  dsimp only [subTimespecNsec] at hnsec
  rw [hsec, hnsec, pure_sepConj_of_true ⟨⟨rfl, rfl⟩, rfl⟩]
  have hstk := cells8_sub64_entails s0.sp st0 st1 st2 st3
    (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 19#5)) st7
  let d := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
  exact entails_subst_frame
    ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗ (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((out + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ R)
    hstk (by sep_entail) (by sep_entail)

/-! ## Full `Timespec::sub_timespec` -/

set_option maxHeartbeats 1600000 in
theorem subTimespec_block_ok [TimePlacement]
    (externs : String → Option (State → State) := fun _ => none) :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 0 externs)
      (timeMultiLib.fnAddr timeMpl timeSubTimespecLocalSym)
      (timeMultiLib.withCodeLoaded timeMpl
        (subTimespecInternalSpec (timeMpl.ρ timeRodataCst16Sym))) := by
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecInternalSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜timeMultiLib.CodeLoaded timeMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn1, hn2⟩, hmem⟩
  by_cases hle : timespecNs s2 n2 ≤ timespecNs s1 n1
  ·
    refine ⟨_, hmem, ?_⟩
    have hge := subTimespec_ge_block_ok (externs := externs)
    rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hge
    refine SepWP.call_subroutine_frame hge
      (x := (out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2))
      (F := (timeMpl.ρ timeRodataCst16Sym ↦ᵣ timePlacedData0) ∗ memRegion (s0.sp - 128#64) 64)
      hpc hrun hsp rfl
      (fun R' hm' => ?_)
      (by rintro R' sf - hp; dsimp only [subTimespecGeSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
      (by rintro R' code sf - he; dsimp only [subTimespecGeSpec] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
      (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    · refine Satisfies.mono ?_ hm'
      dsimp only [subTimespecGeSpec]
      rw [pure_sepConj_of_true ⟨hx0, hx1, hx2, hn1, hn2, hle⟩,
        stackAt_shrink s0.sp 128 64 (by decide)]
      sep_entail
    · refine SepWP.done hpc_sf hrun_sf ⟨fun hm_f => Satisfies.mono ?_ hm_f, hsp_sf, hcs_sf⟩
      dsimp only [subTimespecGeSpec]
      simp only [hle, ↓reduceIte]
      rw [stackAt_shrink s0.sp 128 64 (by decide)]
      sep_entail
  ·
    have hlt : timespecNs s1 n1 < timespecNs s2 n2 := by omega
    have hle_swap : timespecNs s1 n1 ≤ timespecNs s2 n2 := timespec_le_of_lt hlt
    refine ⟨_, hmem, ?_⟩
    change SepWP (timePC00.rebase timePl00.base externs) (s0.readReg64 .lr) s0 _ _ _
    have hpc0 : s0.pc = timePl00.base := hpc; clear hpc; rename_i hpc
    have htbz : ((subTimespecCmpWord s1 s2 n1 n2).getLsbD 0 == false) = true :=
      subTimespec_tbz_eq_true_of_lt hn1 hn2 hlt
    dsimp only [subTimespecCmpWord] at htbz
    wp_conv_pre =>
      rw [stackAt_frame s0.sp 128 8 (by decide),
        show timeRodataCst16Sym = "rust_time:.rodata.cst16+0x0" from rfl,
        ← timePl00_rho_cst16, timePlacedData0_pointsToBytesRO_eq]
      simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, ProofLib.cells_sub_succ,
        ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
      SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
      SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
      SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 => ?_
    wp_conv_pre =>
      rw [pointsTo64_split32 (s0.sp - 48#64) st2,
        show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith]
    apply SepWP.cut (mid := timePl00.base)
    wp_sym_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm])
      (by simpa [arm64_norm] using hrun) ?_
    have hge := subTimespec_ge_block_ok (externs := externs)
    rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hge
    change subroutine_ok (timePC00.rebase timePl00.base externs) timePl00.base subTimespecGeSpec at hge
    refine SepWP.call_subroutine_frame hge
      (x := (s0.sp - 64#64, p2, p1, s2, n2, s1, n1, st0, st1, st2.extractLsb' 0 32))
      (F := ((s0.sp - 44#64) ↦₃₂ st2.extractLsb' 32 32) ∗
            ((s0.sp - 40#64) ↦₆₄ st3) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
            ((s0.sp - 8#64) ↦₆₄ st7) ∗
            (timePl00.ρ "rust_time:.rodata.cst16+0x0" ↦₆₄ᵣ 1#64) ∗
            ((timePl00.ρ "rust_time:.rodata.cst16+0x0" + 8#64) ↦₆₄ᵣ 0#64) ∗
            (out ↦₆₄ ow0) ∗ ((out + 8#64) ↦₆₄ ow1) ∗ ((out + 16#64) ↦₃₂ ow2))
      (by simp [wp_norm, arm64_norm])
      (by simpa [arm64_norm] using hrun)
      (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
      (by simp only [wp_norm, arm64_norm]; rfl)
      (fun R' hm' => ?_)
      (by rintro R' sf - hp; dsimp only [subTimespecGeSpec] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
      (by rintro R' code sf - he; dsimp only [subTimespecGeSpec] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
    · refine Satisfies.mono ?_ hm'
      dsimp only [subTimespecGeSpec]
      rw [pure_sepConj_of_true ⟨by simp [wp_norm, arm64_norm],
          by simp [wp_norm, arm64_norm],
          by simp [wp_norm, arm64_norm],
          hn2, hn1, hle_swap⟩,
        show (((((((((((((((((s0.writeReg64 Reg.sp (s0.sp - 64#64)).writeReg64 (.gpr 29#5) (s0.sp - 32#64)).writeReg64
            (.gpr 12#5) (BitVec.zeroExtend 64 n1)).writeReg64 (.gpr 10#5) (BitVec.zeroExtend 64 n2)).writeReg64
            (.gpr 19#5) out).writeReg64 (.gpr 9#5) s1).writeReg64 (.gpr 11#5) s2).writeReg64
            (.gpr 14#5) (if s1.slt s2 = true then 0#64 else 1#64)).writeReg64 (.gpr 13#5)
            (if (s1 == s2) = true then if n1.ult n2 = true then 0#64 else 1#64
             else if s1.slt s2 = true then 0#64 else 1#64)).writeReg64 (.gpr 8#5) p1).writeReg64
            (.gpr 0#5) (s0.sp - 64#64)).writeReg64 (.gpr 1#5) p2).writeReg64 (.gpr 2#5) p1).writeReg64
            (.gpr 30#5) (timePl00.base + 172#64)).setPState (subsPState64 s1 s2)).setPC
            timePl00.base).setMem m_1).sp = s0.sp - 64#64 by simp [wp_norm, arm64_norm],
        show s0.sp - 64#64 + 8#64 = s0.sp - 56#64 by bv_arith,
        show s0.sp - 64#64 + 16#64 = s0.sp - 48#64 by bv_arith]
      sep_entail
    · dsimp only [subTimespecGeSpec]
      wp_conv_pre =>
        simp only [sepConj_assoc]
      refine SepWP.pure_elim ?_
      rintro ⟨⟨htr1, hsig1⟩, hfs1⟩
      replace htr1 : sf1.trace = s0.trace := by simpa [wp_norm, arm64_norm] using htr1
      replace hsig1 : sf1.sigActions = s0.sigActions := by simpa [wp_norm, arm64_norm] using hsig1
      replace hfs1 : sf1.fs = s0.fs := by simpa [wp_norm, arm64_norm] using hfs1
      have hsp1_eq : sf1.sp = s0.sp - 64#64 := by simpa [wp_norm, arm64_norm] using hsp1
      have hsp1_al : sf1.spAligned = true := by
        simpa only [State.spAligned, hsp1_eq, wp_norm, arm64_norm] using hsp
      rw [CalleeSavedPreserved.iff_regs] at hcs1
      rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _hfp_1, hvregs_1⟩
      have hx19_out : sf1.readReg64 (.gpr 19#5) = out := by
        simpa [wp_norm, arm64_norm, hx0] using hx19_1
      apply timePC00_adrp_0xac timePl00.base externs rfl hpc1 hrun1
      wp_conv_pre =>
        simp only [State.setMem, State.setPC, State.setPState, wp_norm, arm64_norm]
        rw [timespec_sub_natAbs_comm (timespecNs s1 n1) (timespecNs s2 n2)]
      wp_sym_steps
      refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
      refine ⟨?_,
        by simp only [wp_norm, arm64_norm],
        by
          rw [CalleeSavedPreserved.iff_regs]
          refine ⟨by simp [wp_norm, arm64_norm],
            by simpa [wp_norm, arm64_norm] using hx20_1,
            by simpa [wp_norm, arm64_norm] using hx21_1,
            by simpa [wp_norm, arm64_norm] using hx22_1,
            by simpa [wp_norm, arm64_norm] using hx23_1,
            by simpa [wp_norm, arm64_norm] using hx24_1,
            by simpa [wp_norm, arm64_norm] using hx25_1,
            by simpa [wp_norm, arm64_norm] using hx26_1,
            by simpa [wp_norm, arm64_norm] using hx27_1,
            by simpa [wp_norm, arm64_norm] using hx28_1,
            by simp [wp_norm, arm64_norm],
            by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvregs_1⟩⟩
      intro hm_f
      refine Satisfies.mono ?_ hm_f
      let d := (timespecNs s1 n1 - timespecNs s2 n2).natAbs
      simp only [hle, ↓reduceIte]
      rw [pure_sepConj_of_true ⟨⟨by simpa [State.writeVReg128, wp_norm, arm64_norm] using htr1,
          by simpa [State.writeVReg128, wp_norm, arm64_norm] using hsig1⟩,
        by simpa [State.writeVReg128, wp_norm, arm64_norm] using hfs1⟩]
      simp only [eor_cst16_truncate64, eor_cst16_extractHi64,
        show timeRodataCst16Sym = "rust_time:.rodata.cst16+0x0" from rfl,
        ← timePl00_rho_cst16, timePlacedData0_pointsToBytesRO_eq]
      have hpair := pointsTo32_pair (s0.sp - 48#64) (BitVec.ofNat 32 (d % 10 ^ 9)) (st2.extractLsb' 32 32)
      rw [show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith] at hpair
      have hstk := frame128_entails s0.sp 0#64 (BitVec.ofNat 64 (d / 10 ^ 9))
        (st2.extractLsb' 32 32 ++ BitVec.ofNat 32 (d % 10 ^ 9)) st3
        (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 19#5)) st7
      rw [← hpair] at hstk
      exact entails_subst_frame
        ((p1 ↦₆₄ s1) ∗ ((p1 + 8#64) ↦₃₂ n1) ∗ (p2 ↦₆₄ s2) ∗ ((p2 + 8#64) ↦₃₂ n2) ∗
          (timePl00.ρ "rust_time:.rodata.cst16+0x0" ↦₆₄ᵣ 1#64) ∗
          ((timePl00.ρ "rust_time:.rodata.cst16+0x0" + 8#64) ↦₆₄ᵣ 0#64) ∗
          (out ↦₆₄ 1#64) ∗ ((out + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
          ((out + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ R)
        hstk (by sep_entail) (by sep_entail)

/-! ## `SystemTime::duration_since` -/

set_option maxHeartbeats 1600000 in
theorem timeDurationSince_block_ok [TimePlacement]
    (externs : String → Option (State → State) := fun _ => none) :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 1 externs)
      (timeMultiLib.fnAddr timeMpl timeDurationSinceSym)
      (timeMultiLib.withCodeLoaded timeMpl
        (timeDurationSinceSpec (timeMpl.ρ timeRodataCst16Sym))) := by
  rw [timeFnAddr_eq_base 1 timeDurationSinceSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, s2, n2, ret, sp, s1, n1, b20⟩ R s0 hpc hrun hpre hsp
  dsimp only [MultiPlacedLib.withCodeLoaded, timeDurationSinceSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜timeMultiLib.CodeLoaded timeMpl s0.mem⌝, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx8, hsp_eq, hn1, hn2⟩, hmem⟩
  subst hsp_eq
  refine ⟨_, hmem, ?_⟩
  apply seqCodeLoaded hcl (mid := timePl00.base)
  change SepWP (timePC01.rebase timePl01.base externs) timePl00.base s0 _ _ _
  have hpc0 : s0.pc = timePl01.base := hpc; clear hpc; rename_i hpc
  have hx2_tr : BitVec.truncate 32 (s0.readReg64 (.gpr 2#5)) = n2 := hx2
  wp_conv_pre =>
    rw [← stackAt_eq_stackFrameAt s0.sp 208, stackAt_frame s0.sp 208 10 (by decide)]
    simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, ProofLib.cells_sub_succ,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
    SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 =>
    SepWP.exists_elim fun st8 => SepWP.exists_elim fun st9 => ?_
  wp_conv_pre =>
    rw [memRegion20_eq_sret_slots ret]
    simp only [sepExists_sepConj_right]
  refine SepWP.exists_elim fun ow2 => SepWP.exists_elim fun ow1 =>
    SepWP.exists_elim fun ow0 => ?_
  wp_conv_pre =>
    rw [pointsTo64_split32 (s0.sp - 72#64) st1,
      show s0.sp - 72#64 + 4#64 = s0.sp - 68#64 by bv_arith,
      pointsTo64_split32 (s0.sp - 48#64) st4,
      show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith]
  wp_sym_steps
  refine SepWP.done
    (by
      dsimp only [State.setMem, State.setPC]
      rw [timePl01_rho_subTimespec]
      bv_omega)
    (by simpa [arm64_norm] using hrun)
    fun hcl_call => ?_
  have hsub := MultiPlacedLib.subroutine_ok_of_block_hooks
    (P := timeMultiLib.blockProgram timeMpl 1 externs) (j := 0) (by decide)
    (subTimespec_block_ok (externs := externs))
    (timeMultiLib.externAt?_blockProgram_eq_of_externs_eq rfl) rfl
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hsub
  change subroutine_ok (timePC01.rebase timePl01.base externs) timePl00.base _ at hsub
  change SepWP (timePC01.rebase timePl01.base externs) (s0.readReg64 .lr) _ _ _ _
  refine SepWP.call_subroutine_frame hsub
    (x := (s0.sp - 64#64, p, s0.sp - 80#64, s1, n1, s2, n2, st2, st3, st4.extractLsb' 0 32))
    (F := ((ret + 20#64) ↦₃₂ b20) ∗
          ((s0.sp - 68#64) ↦₃₂ st1.extractLsb' 32 32) ∗
          ((s0.sp - 44#64) ↦₃₂ st4.extractLsb' 32 32) ∗
          ((s0.sp - 40#64) ↦₆₄ st5) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ st9) ∗
          (ret ↦₆₄ ow0) ∗ ((ret + 8#64) ↦₆₄ ow1) ∗ ((ret + 16#64) ↦₃₂ ow2))
    (by
      dsimp only [State.setMem, State.setPC]
      rw [timePl01_rho_subTimespec]
      bv_omega)
    (by simpa [arm64_norm] using hrun)
    (by simpa only [State.spAligned, wp_norm, arm64_norm] using hsp)
    (by simp only [wp_norm, arm64_norm]; rfl)
    (fun R' hm' => ?_)
    (by
      rintro R' sf - hp
      dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecInternalSpec] at hp
      rw [satisfies_pure_sepConj] at hp
      exact hp.1)
    (by
      rintro R' code sf - he
      dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecInternalSpec] at he
      rw [satisfies_pure_sepConj] at he
      exact he.1)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · refine Satisfies.mono ?_ hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecInternalSpec]
    rw [sepConj_comm _ ⌜timeMultiLib.CodeLoaded timeMpl _⌝,
      pure_sepConj_of_true hcl_call,
      pure_sepConj_of_true ⟨by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        hn1, hn2⟩]
    simp only [wp_norm, arm64_norm]
    sep_entail
  · dsimp only [MultiPlacedLib.withCodeLoaded, subTimespecInternalSpec]
    wp_conv_pre =>
      simp only [sepConj_assoc]
    refine SepWP.pure_elim ?_
    rintro ⟨⟨htr1, _hsig1⟩, hfs1⟩
    replace htr1 : sf1.trace = s0.trace := by simpa [wp_norm, arm64_norm] using htr1
    replace hfs1 : sf1.fs = s0.fs := by simpa [wp_norm, arm64_norm] using hfs1
    replace hpc1 : sf1.pc = timePl01.base + 48#64 := by simpa [wp_norm, arm64_norm] using hpc1
    have hsp1_eq : sf1.sp = s0.sp - 80#64 := by simpa [wp_norm, arm64_norm] using hsp1
    have hsp1_al : sf1.spAligned = true := by
      simpa only [State.spAligned, hsp1_eq, wp_norm, arm64_norm] using hsp
    rw [CalleeSavedPreserved.iff_regs] at hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _hfp_1, hvregs_1⟩
    have hx19_ret : sf1.readReg64 (.gpr 19#5) = ret := by
      simpa [wp_norm, arm64_norm, hx8] using hx19_1
    wp_conv_pre =>
      simp only [State.setMem, State.setPC, wp_norm, arm64_norm]
    wp_sym_steps
    refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun1]) ?_
    refine ⟨?_,
      by simp only [wp_norm, arm64_norm],
      by
        rw [CalleeSavedPreserved.iff_regs]
        refine ⟨by simp [wp_norm, arm64_norm],
          by simpa [wp_norm, arm64_norm] using hx20_1,
          by simpa [wp_norm, arm64_norm] using hx21_1,
          by simpa [wp_norm, arm64_norm] using hx22_1,
          by simpa [wp_norm, arm64_norm] using hx23_1,
          by simpa [wp_norm, arm64_norm] using hx24_1,
          by simpa [wp_norm, arm64_norm] using hx25_1,
          by simpa [wp_norm, arm64_norm] using hx26_1,
          by simpa [wp_norm, arm64_norm] using hx27_1,
          by simpa [wp_norm, arm64_norm] using hx28_1,
          by simp [wp_norm, arm64_norm],
          by simpa [calleeSavedVRegs, wp_norm, arm64_norm] using hvregs_1⟩⟩
    intro hm_f
    refine Satisfies.mono ?_ hm_f
    let t1 := timespecNs s1 n1
    let t2 := timespecNs s2 n2
    let d := (t1 - t2).natAbs
    let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
    rw [pure_sepConj_of_true ⟨by simpa [wp_norm, arm64_norm] using htr1,
      by simpa [wp_norm, arm64_norm] using hfs1⟩]
    have hpair1 := pointsTo32_pair (s0.sp - 72#64) n2 (st1.extractLsb' 32 32)
    rw [show s0.sp - 72#64 + 4#64 = s0.sp - 68#64 by bv_arith] at hpair1
    have hpair4 := pointsTo32_pair (s0.sp - 48#64) (BitVec.ofNat 32 (d % 10 ^ 9)) (st4.extractLsb' 32 32)
    rw [show s0.sp - 48#64 + 4#64 = s0.sp - 44#64 by bv_arith] at hpair4
    have hstk := frame208_entails s0.sp s2 (st1.extractLsb' 32 32 ++ n2)
      tag (BitVec.ofNat 64 (d / 10 ^ 9))
      (st4.extractLsb' 32 32 ++ BitVec.ofNat 32 (d % 10 ^ 9)) st5
      (s0.readReg64 (.gpr 29#5)) (s0.readReg64 (.gpr 30#5)) (s0.readReg64 (.gpr 19#5)) st9
    rw [← hpair1, ← hpair4] at hstk
    exact entails_subst_frame
      ((p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ ((ret + 20#64) ↦₃₂ b20) ∗
        (timeMpl.ρ timeRodataCst16Sym ↦ᵣ timePlacedData0) ∗
        (ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
        ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ R)
      hstk (by sep_entail) (by sep_entail)

end

/-- Layout-generic `MultiPlacedLib.subroutineOk` correctness theorem for
    `SystemTime::duration_since` (`timeDurationSinceSym` in `VerifiedLibraries.RustStd.timeMultiLib`)
    against `timeDurationSinceSpec`, polymorphic over any external hook table `externs`. -/
theorem timeDurationSince_subroutineOk
    (externs : String → Option (State → State) := fun _ => none) :
    timeMultiLib.subroutineOk timeDurationSinceSym
      (fun mpl => timeDurationSinceSpec (mpl.ρ timeRodataCst16Sym)) externs :=
  ⟨by decide, 1, 0, by decide, fun mpl hpl =>
    @timeDurationSince_block_ok ⟨mpl, hpl⟩ externs⟩

end VerifiedLibraries.RustStd
