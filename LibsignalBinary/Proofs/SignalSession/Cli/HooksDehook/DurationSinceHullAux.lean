/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.RustStd.DurationSinceBoundedVm -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
import ProofLib.Hoare.Model
import ProofLib.SepLogic.WP.StepsProcess

/-!
# Two-Block Engine & `stripS` Lifting Helpers for `DurationSinceCode` (`HooksDehook.DurationSinceHullAux`)

Auxiliary untrusted (`Role::Proof`) lemmas backing `HooksDehook.DurationSinceCode`:
1. Two-block (`block 0` `Timespec::sub_timespec` + `block 1` `SystemTime::duration_since`)
   placement-generic correctness `timeDurationSince_only01_ok` **without** `timeMultiLib.withCodeLoaded`,
   eliminating any `CodeLoaded` obligation on `timeMultiLib` block `2` (`SystemTime::add`).
2. `keep01`, `strip_codeLoaded_of_imp`, `fetch_in_block_not_svc0_msr`, and
   `steps_pureMem_lift_stripS_vm` lifting pure `stripS` runs back to an arbitrary hook-free
   `P_sub` while establishing `NonSyscallPreserved` and `tpidrEl0` preservation.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceHullAux

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open VerifiedLibraries.RustStd (
  IoFrame TimePlacement timeMpl timePl00 timePl01 timePC00 timePC01
  timespecNs timePlacedData0 timeMultiLib timeSubTimespecLocalSym
  timeRodataCst16Sym timeFnAddr_eq_base timePl00_rho_cst16 timePl01_rho_subTimespec
  subTimespecGeSpec subTimespecInternalSpec subTimespec_ge_block_ok
  subTimespecCmpWord subTimespec_tbz_eq_true_of_lt timespec_le_of_lt timespec_sub_natAbs_comm
  timePlacedData0_pointsToBytesRO_eq timePC00_adrp_0xac
  eor_cst16_truncate64 eor_cst16_extractHi64
  frame128_entails frame208_entails memRegion20_eq_sret_slots
)

/-- Argument tuple `(p, s2, n2, ret, s1, n1, b20)` for `durCore01Spec`. -/
abbrev DurCoreArgs : Type :=
  BitVec 64 × BitVec 64 × BitVec 32 × BitVec 64 × BitVec 64 × BitVec 32 × BitVec 32

/-- Block-`0` + block-`1` internal contract for `SystemTime::duration_since` requiring only
    `blockProgram mpl 0` (`Timespec::sub_timespec`) `CodeLoaded`, never block `2`. -/
@[expose] def durCore01Spec (mpl : MultiPlacement) : Spec DurCoreArgs where
  pre := fun ⟨p, s2, n2, ret, s1, n1, b20⟩ s0 =>
    ⌜(timeMultiLib.blockProgram mpl 0).CodeLoaded s0.mem⌝ ∗
      ((mpl.ρ timeRodataCst16Sym) ↦ᵣ timePlacedData0) ∗
      (⌜s0.readReg64 .x0 = p ∧
          s0.readReg64 .x1 = s2 ∧
          (s0.readReg64 .x2).truncate 32 = n2 ∧
          s0.readReg64 .x8 = ret ∧
          n1.toNat < 10 ^ 9 ∧
          n2.toNat < 10 ^ 9⌝ ∗
        (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
        memRegion ret 20 ∗ ((ret + 20#64) ↦₃₂ b20) ∗
        stackAt s0.sp 208)
  post := fun ⟨p, s2, n2, ret, s1, n1, b20⟩ s0 sf =>
    let t1 := timespecNs s1 n1
    let t2 := timespecNs s2 n2
    let d := (t1 - t2).natAbs
    let tag : BitVec 64 := if t2 ≤ t1 then 0#64 else 1#64
    ⌜IoFrame s0 sf ∧ sf.fs = s0.fs⌝ ∗
      ((mpl.ρ timeRodataCst16Sym) ↦ᵣ timePlacedData0) ∗
      (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
      (ret ↦₆₄ tag) ∗
      ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
      ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗
      ((ret + 20#64) ↦₃₂ b20) ∗
      stackAt s0.sp 208
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

section TwoBlockSteps
arm64_proof_prelude

private theorem entails_subst_frame {A B : SepProp} (F : SepProp) {P Q : SepProp}
    (hab : A ⊢ B) (h1 : P ⊢ A ∗ F) (h2 : B ∗ F ⊢ Q) : P ⊢ Q :=
  Arm64.Entails.trans h1 (Arm64.Entails.trans (sepConj_mono_left hab) h2)

set_option maxHeartbeats 1600000 in
/-- Block-`0` `Timespec::sub_timespec` correctness **without** `timeMultiLib.withCodeLoaded`
    (eliminating the unused `CodeLoaded` precondition on block `2` `SystemTime::add`). -/
theorem subTimespec_only0_ok [TimePlacement] :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 0)
      (timeMultiLib.fnAddr timeMpl timeSubTimespecLocalSym)
      (subTimespecInternalSpec (timeMpl.ρ timeRodataCst16Sym)) := by
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)]
  apply subroutine_ok_of_sepWP_init
  rintro ⟨out, p1, p2, s1, n1, s2, n2, ow0, ow1, ow2⟩ R s0 hpc hrun hpre hsp
  dsimp only [subTimespecInternalSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hn1, hn2⟩, hmem⟩
  by_cases hle : timespecNs s2 n2 ≤ timespecNs s1 n1
  · refine ⟨_, hmem, ?_⟩
    have hge := subTimespec_ge_block_ok (externs := fun _ => none)
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
  · have hlt : timespecNs s1 n1 < timespecNs s2 n2 := by omega
    have hle_swap : timespecNs s1 n1 ≤ timespecNs s2 n2 := timespec_le_of_lt hlt
    refine ⟨_, hmem, ?_⟩
    change SepWP (timePC00.rebase timePl00.base (fun _ => none)) (s0.readReg64 .lr) s0 _ _ _
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
    have hge := subTimespec_ge_block_ok (externs := fun _ => none)
    rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hge
    change subroutine_ok (timePC00.rebase timePl00.base (fun _ => none)) timePl00.base subTimespecGeSpec at hge
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
      apply timePC00_adrp_0xac timePl00.base (fun _ => none) rfl hpc1 hrun1
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

private theorem seq_oneCodeLoaded {prog Q : Program} {mid target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : Q.CodeLoaded s.mem)
    (h : SepWP prog mid s Pre
      (fun sm Pm => Q.CodeLoaded sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL_P => ?_
  obtain ⟨sm, hsteps1, hout1⟩ := SepWP.to_reaches_pc h hm hL_P
  rcases hout1 with ⟨_, _, _, hmm, hcont⟩ | ⟨hrun_m, hoom⟩
  · obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc
      (hcont (hsteps1.codeLoaded hcl)) hmm (hsteps1.codeLoaded hL_P)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hrun_m, hoom⟩⟩

set_option maxHeartbeats 1600000 in
/-- Block-`1` `SystemTime::duration_since` correctness requiring **only** block `0`
    (`Timespec::sub_timespec`) `CodeLoaded`, never block `2` (`SystemTime::add`). -/
theorem timeDurationSince_only01_ok [TimePlacement] :
    subroutine_ok (timeMultiLib.blockProgram timeMpl 1)
      (timeMpl.base 1)
      (durCore01Spec timeMpl) := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, s2, n2, ret, s1, n1, b20⟩ R s0 hpc hrun hpre hsp
  dsimp only [durCore01Spec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hro_rest⟩
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = s2 ∧
        (s0.readReg64 .x2).truncate 32 = n2 ∧ s0.readReg64 .x8 = ret ∧
        n1.toNat < 10 ^ 9 ∧ n2.toNat < 10 ^ 9⌝ ∗
      (((timeMpl.ρ timeRodataCst16Sym ↦ᵣ timePlacedData0) ∗
        (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗
        memRegion ret 20 ∗ ((ret + 20#64) ↦₃₂ b20) ∗ stackAt s0.sp 208) ∗ R) := by
    ac_nf at hro_rest ⊢
  rw [satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1, hx2, hx8, hn1, hn2⟩, hmem⟩
  refine ⟨_, hmem, ?_⟩
  apply seq_oneCodeLoaded hcl0 (mid := timePl00.base)
  change SepWP (timePC01.rebase timePl01.base (fun _ => none)) timePl00.base s0 _ _ _
  have hpc0 : s0.pc = timePl01.base := hpc; clear hpc; rename_i hpc
  have hx2_tr : BitVec.truncate 32 (s0.readReg64 (.gpr 2#5)) = n2 := hx2
  wp_conv_pre =>
    rw [stackAt_frame s0.sp 208 10 (by decide)]
    simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, ProofLib.cells_sub_succ,
      ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWP.exists_elim fun st0 => SepWP.exists_elim fun st1 =>
    SepWP.exists_elim fun st2 => SepWP.exists_elim fun st3 =>
    SepWP.exists_elim fun st4 => SepWP.exists_elim fun st5 =>
    SepWP.exists_elim fun st6 => SepWP.exists_elim fun st7 =>
    SepWP.exists_elim fun st8 => SepWP.exists_elim fun st9 => ?_
  wp_conv_pre =>
    rw [memRegion20_eq_sret_slots ret]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
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
    fun hcl0_call => ?_
  have hsub0 := subTimespec_only0_ok
  rw [timeFnAddr_eq_base 0 timeSubTimespecLocalSym (by decide) (by decide)] at hsub0
  have hsub : subroutine_ok (timeMultiLib.blockProgram timeMpl 1) timePl00.base
      ( { subTimespecInternalSpec (timeMpl.ρ timeRodataCst16Sym) with
          pre := fun y st =>
            ⌜(timeMultiLib.blockProgram timeMpl 0).CodeLoaded st.mem⌝ ∗
              (subTimespecInternalSpec (timeMpl.ρ timeRodataCst16Sym)).pre y st } ) := by
    simp only [subroutine_ok_iff, reaches_outcome_iff]
    intro y Ry st hpst hrst hprst hspst _hL1
    rw [sepConj_assoc, satisfies_pure_sepConj] at hprst
    obtain ⟨stf, hsteps0, hout0⟩ := reaches_outcome_iff.1
      (subroutine_ok_iff.1 hsub0 y Ry st hpst hrst hprst.2 hspst) hprst.1
    refine ⟨stf, Steps.of_sameHooks
      (P := timeMultiLib.blockProgram timeMpl 1) (Q := timeMultiLib.blockProgram timeMpl 0)
      (timeMultiLib.externAt?_blockProgram_eq_of_externs_eq rfl) rfl hsteps0, hout0⟩
  change subroutine_ok (timePC01.rebase timePl01.base (fun _ => none)) timePl00.base _ at hsub
  change SepWP (timePC01.rebase timePl01.base (fun _ => none)) (s0.readReg64 .lr) _ _ _ _
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
      dsimp only [subTimespecInternalSpec] at hp
      rw [satisfies_pure_sepConj] at hp
      exact hp.1)
    (by
      rintro R' code sf - he
      dsimp only [subTimespecInternalSpec] at he
      rw [satisfies_pure_sepConj] at he
      exact he.1)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · refine Satisfies.mono ?_ hm'
    dsimp only [subTimespecInternalSpec]
    rw [pure_sepConj_of_true hcl0_call,
      pure_sepConj_of_true ⟨by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        by simp [wp_norm, arm64_norm],
        hn1, hn2⟩]
    simp only [wp_norm, arm64_norm]
    sep_entail
  · dsimp only [subTimespecInternalSpec]
    wp_conv_pre =>
      simp only [sepConj_assoc]
    refine SepWP.pure_elim ?_
    rintro ⟨⟨htr1, hsig1⟩, hfs1⟩
    replace htr1 : sf1.trace = s0.trace := by simpa [wp_norm, arm64_norm] using htr1
    replace hsig1 : sf1.sigActions = s0.sigActions := by simpa [wp_norm, arm64_norm] using hsig1
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
    rw [pure_sepConj_of_true ⟨⟨by simpa [wp_norm, arm64_norm] using htr1,
        by simpa [wp_norm, arm64_norm] using hsig1⟩,
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
    rw [stackAt_eq_stackFrameAt s0.sp 208 (by decide)]
    exact entails_subst_frame
      (((timeMpl.ρ timeRodataCst16Sym) ↦ᵣ timePlacedData0) ∗
        (p ↦₆₄ s1) ∗ ((p + 8#64) ↦₃₂ n1) ∗ ((ret + 20#64) ↦₃₂ b20) ∗
        (ret ↦₆₄ tag) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (d / 10 ^ 9)) ∗
        ((ret + 16#64) ↦₃₂ BitVec.ofNat 32 (d % 10 ^ 9)) ∗ R)
      hstk (by sep_entail) (by sep_entail)

end TwoBlockSteps

/-- `keep` mask covering `timeMultiLib` blocks `0` (`sub_timespec`) and `1` (`duration_since`). -/
@[expose] def keep01 (mpl : MultiPlacement) (a : BitVec 64) : Bool :=
  progKeep (timeMultiLib.blockProgram mpl 0) a || progKeep (timeMultiLib.blockProgram mpl 1) a

/-- Preserve `P.CodeLoaded` under `stripExecOutside keep` whenever `progKeep P` implies `keep`. -/
theorem strip_codeLoaded_of_imp {P : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hcl : P.CodeLoaded m) (himp : ∀ a, progKeep P a = true → keep a = true) :
    P.CodeLoaded (stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hcl.aligned hcl.no_wrap fun k hk => ?_
  have hno := hcl.no_wrap
  have hsub : P.base + BitVec.ofNat 64 k - P.base = BitVec.ofNat 64 k := by bv_omega
  have hin : (P.base + BitVec.ofNat 64 k - P.base).toNat < P.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk
  have hkp : keep (P.base + BitVec.ofNat 64 k) = true :=
    himp _ (by unfold progKeep; exact decide_eq_true hin)
  have hp_eq : (stripExecOutside keep m).perm (P.base + BitVec.ofNat 64 k) =
      m.perm (P.base + BitVec.ofNat 64 k) := by
    rw [strip_perm, hkp]
    cases m.perm (P.base + BitVec.ofNat 64 k) with
    | none => rfl
    | some p => cases p; rfl
  rw [strip_read8, hp_eq, strip_isLazyFree]
  exact ⟨hcl.byte_eq k hk, hcl.perm_eq k hk, hcl.isLazyFree_eq k hk⟩

private theorem timeMultiLib_patchSafe_svc0 :
    timeMultiLib.blocks.all (fun blk => blk.patchSafe svc0Pat) = true := by decide

private theorem timeMultiLib_patchSafe_msrTpidrEl0 :
    timeMultiLib.blocks.all (fun blk => blk.patchSafe msrTpidrEl0Pat) = true := by decide

/-- Any instruction fetched inside `timeMultiLib` block `j` (`j < 3`) under `KeepsFrozen` is
    neither `svc #0` nor `msr tpidr_el0`. -/
theorem fetch_in_block_not_svc0_msr {mpl : MultiPlacement} {j : Nat}
    (hj : j < timeMultiLib.blocks.length)
    (hpl : timeMultiLib.Placeable mpl)
    {m0 m : Memory} (hcl0 : (timeMultiLib.blockProgram mpl j).CodeLoaded m0)
    (hkf : m0.KeepsFrozen m) {pc : BitVec 64} {inst : Instr}
    (hkp : progKeep (timeMultiLib.blockProgram mpl j) pc = true)
    (hfm : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  have hcl_m : (timeMultiLib.blockProgram mpl j).CodeLoaded m := hcl0.of_keepsFrozen hkf
  have hal_pc : pc.toNat % 4 = 0 := by
    unfold Program.fetchMem at hfm
    by_cases h4 : pc.toNat % 4 = 0
    · exact h4
    · simp [h4] at hfm
  let Pj := timeMultiLib.blockProgram mpl j
  have hcl_Pj : Pj.CodeLoaded m := hcl_m
  have hPj_al : Pj.base.toNat % 4 = 0 := hcl_Pj.aligned
  have hPj_nw : Pj.base.toNat + Pj.code.length ≤ 2 ^ 64 := hcl_Pj.no_wrap
  have hin : (pc - Pj.base).toNat < Pj.code.length := by
    unfold progKeep at hkp; exact of_decide_eq_true hkp
  have hPj_len4 : Pj.code.length % 4 = 0 := by
    have hbt := (hpl.blocks_ok j hj).len_aligned
    have hplen : ((timeMultiLib.blockLib j).text.patched (timeMultiLib.blockPlacement mpl j)).length =
        (timeMultiLib.blockLib j).text.code.length :=
      CodeBlock.length_patched_of_aligned _ (by rw [timeMultiLib.blockLib_text hj]; exact hbt)
    change ((timeMultiLib.blockLib j).text.patched (timeMultiLib.blockPlacement mpl j)).length % 4 = 0
    rw [hplen, timeMultiLib.blockLib_text hj]; exact hbt
  let off := (pc - Pj.base).toNat
  have hpc_eq : pc = Pj.base + BitVec.ofNat 64 off := by dsimp [off]; bv_omega
  have hpc_ge : Pj.base.toNat ≤ pc.toNat := by
    change (pc - Pj.base).toNat < Pj.code.length at hin; bv_omega
  have hoff_nat : off = pc.toNat - Pj.base.toNat := by dsimp [off]; bv_omega
  have hoff_lt : off < Pj.code.length := hin
  have hoff4 : off % 4 = 0 := by omega
  have hrw : Pj.readWordOff off = some (m.read32 pc) := by
    have hb0 := hcl_Pj.byte_eq off (by omega)
    have hb1 := hcl_Pj.byte_eq (off + 1) (by omega)
    have hb2 := hcl_Pj.byte_eq (off + 2) (by omega)
    have hb3 := hcl_Pj.byte_eq (off + 3) (by omega)
    have ha0 : pc + 0#64 = Pj.base + BitVec.ofNat 64 off := by rw [hpc_eq]; bv_omega
    have ha1 : pc + 1#64 = Pj.base + BitVec.ofNat 64 (off + 1) := by rw [hpc_eq]; bv_omega
    have ha2 : pc + 2#64 = Pj.base + BitVec.ofNat 64 (off + 2) := by rw [hpc_eq]; bv_omega
    have ha3 : pc + 3#64 = Pj.base + BitVec.ofNat 64 (off + 3) := by rw [hpc_eq]; bv_omega
    unfold Program.readWordOff
    simp only [hoff4, ne_eq, not_true_eq_false, ↓reduceIte]
    have hd0 : Pj.code.drop off =
        Pj.code[off]'(by omega) :: Pj.code[off + 1]'(by omega) ::
        Pj.code[off + 2]'(by omega) :: Pj.code[off + 3]'(by omega) :: Pj.code.drop (off + 4) := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
        List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rw [hd0]; dsimp only [Memory.read32]
    rw [ha0, hb0, ha1, hb1, ha2, hb2, ha3, hb3]
  have hdec : decode (m.read32 pc) = some inst := by
    unfold Program.fetchMem at hfm
    split at hfm
    · simp at hfm
    · split at hfm
      · simp at hfm
      · split at hfm
        · simp at hfm
        · exact hfm
  have hfetch_Pj : Pj.fetch (Pj.base + BitVec.ofNat 64 off) = some inst := by
    have hf := Program.fetch_of_readWordOff (prog := Pj) (off := off) (by omega)
      (by simp [Pj, MultiPlacedLib.blockProgram, PlacedLib.program, Program.hookAtOff?]) hrw
    rwa [hdec] at hf
  have hps_svc : (timeMultiLib.blockLib j).text.patchSafe svc0Pat = true := by
    rw [timeMultiLib.blockLib_text hj]
    exact (List.all_eq_true.mp timeMultiLib_patchSafe_svc0) _ (List.getElem_mem hj)
  have hps_msr : (timeMultiLib.blockLib j).text.patchSafe msrTpidrEl0Pat = true := by
    rw [timeMultiLib.blockLib_text hj]
    exact (List.all_eq_true.mp timeMultiLib_patchSafe_msrTpidrEl0) _ (List.getElem_mem hj)
  have hall_svc := PlacedLib.program_noSvc0_of_patchSafe hps_svc (timeMultiLib.blockPlacement mpl j)
  have hall_msr := PlacedLib.program_noMsrTpidrEl0_of_patchSafe hps_msr (timeMultiLib.blockPlacement mpl j)
  exact ⟨by simpa using Program.fetch_of_allInstrs hall_svc _ _ hfetch_Pj,
    by simpa using Program.fetch_of_allInstrs hall_msr _ _ hfetch_Pj⟩

/-- Lift a `Running`-terminated `Steps Program.pureMem (stripS keep s0) sf'` run to `Steps P s0 sf`
    while simultaneously recording `NonSyscallPreserved s0 sf` and `sf.tpidrEl0 = s0.tpidrEl0`. -/
theorem steps_pureMem_lift_stripS_vm (keep : BitVec 64 → Bool) {P : Program} {m0 : Memory}
    (hsvc_P : P.svc = Syscall.standard)
    (hext_P : ∀ pc : BitVec 64, keep pc = true → P.externAt? pc = none)
    (h_pure : ∀ (m : Memory) (pc : BitVec 64) (inst : Instr),
      m0.KeepsFrozen m → keep pc = true → Program.pureMem.fetchMem m pc = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false) :
    ∀ {s0 s' sf' : State},
      s' = stripS keep s0 → m0.KeepsFrozen s0.mem →
      Steps Program.pureMem s' sf' → sf'.status = .Running →
      ∃ sf : State, sf' = stripS keep sf ∧ Steps P s0 sf ∧
        ProofLib.NonSyscallPreserved s0 sf ∧ sf.tpidrEl0 = s0.tpidrEl0 := by
  intro s0 s' sf' hs' hkf hsteps hrun_f
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProofLib.NonSyscallPreserved.refl s0, rfl⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hrun2' : s2'.status = .Running := by
      cases hrest with
      | refl _ => exact hrun_f
      | step hs _ => exact hs.status_running
    cases hstep with
    | halt_unmapped _ _ _ => simp at hrun2'
    | extern _ h_ext _ _ => nomatch h_ext
    | extern_fault _ h_ext _ => nomatch h_ext
    | exec hrun1' hfetch' =>
      rename_i inst
      have hrun1 : s0.status = .Running := by cases s0; exact hrun1'
      have hpc_eq : (stripS keep s0).pc = s0.pc := by cases s0; rfl
      have hmem_eq : (stripS keep s0).mem = stripExecOutside keep s0.mem := by cases s0; rfl
      rw [hpc_eq, hmem_eq] at hfetch'
      unfold Program.fetchMem at hfetch'
      by_cases hce' : (stripExecOutside keep s0.mem).canExec s0.pc 4 = true
      · have hr32 : (stripExecOutside keep s0.mem).read32 s0.pc = s0.mem.read32 s0.pc := by
          simp [Memory.read32, strip_read8]
        simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr32] at hfetch'
        have hx4 :
            ((stripExecOutside keep s0.mem).perm s0.pc).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 1#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 2#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 3#64)).x = true := by
          simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
        obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
        obtain ⟨hx1, _⟩ := strip_perm_x_imp hx4.2.1
        obtain ⟨hx2, _⟩ := strip_perm_x_imp hx4.2.2.1
        obtain ⟨hx3, _⟩ := strip_perm_x_imp hx4.2.2.2
        have hce : s0.mem.canExec s0.pc 4 = true := by
          simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
        have hpure_ext : Program.pureMem.externAt? s0.pc = none := rfl
        have hfetch_pm : Program.pureMem.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem; rw [hpure_ext] at hfetch' ⊢; simpa [hce] using hfetch'
        have hfetch_P : P.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem; rw [hext_P s0.pc hk0]
          unfold Program.fetchMem at hfetch_pm; rw [hpure_ext] at hfetch_pm; exact hfetch_pm
        obtain ⟨hns, hmsr⟩ := h_pure s0.mem s0.pc inst hkf hk0 hfetch_pm
        rw [evalInst_pureMem] at hrest hrun2' ih
        have heval_P : P.evalInst inst s0 = execInst inst s0 :=
          evalInst_eq_execInst_of_not_isSvc0 hns s0
        have hstep_s0 : Step P s0 (execInst inst s0) := heval_P ▸ Step.exec hrun1 hfetch_P
        have hstep_pm : Step Program.pureMem s0 (execInst inst s0) :=
          evalInst_pureMem inst s0 ▸ Step.exec hrun1 hfetch_pm
        have _ := hsvc_P
        have hcomm : execInst inst (stripS keep s0) = stripS keep (execInst inst s0) :=
          execInst_stripS hns keep s0
        have hnsp1 : ProofLib.NonSyscallPreserved s0 (execInst inst s0) :=
          ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s0
        have htp1 : (execInst inst s0).tpidrEl0 = s0.tpidrEl0 :=
          execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s0
        obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest, htp_rest⟩ :=
          ih hcomm (hkf.trans hstep_pm.keepsFrozen) hrun_f
        exact ⟨sf, hsf_eq, Steps.step hstep_s0 hsteps_rest, hnsp1.trans hnsp_rest,
          htp_rest.trans htp1⟩
      · simp [hce'] at hfetch'

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.DurationSinceHullAux
