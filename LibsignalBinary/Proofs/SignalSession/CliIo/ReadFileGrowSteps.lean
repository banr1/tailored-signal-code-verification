/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps
public import LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps
public meta import ProofLib.ProgramReflection

/-!
# Bounded `read_file` Growth and `memcpy` Step Lemmas

Proves the capacity-doubling sub-loop (`+0x124`), `finish_grow` join (`+0x1b0`), and `memcpy`
back-edge (`+0x15c → +0xd8`) step lemmas for `signalSessionIoMultiLib` block `3`
(`signal_session_io::read_file`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileGrowSteps

open Arm64 Arm64.Obj Arm64.Process ProofLib
  ProofLib.ProgramReflection ProofLib.GenPlacedFetches ProofLib.StdStartup
open CryptoVerification (signalSessionIoMultiLib)
open VerifiedLibraries.RustStd (
  RustStdAlloc NullAllowed
  PoolPreserved AllocCallPreserved IoFrame StdErrnoCell stdErrnoAddr
  vecHeader ioVecBuf allocFinishGrowSpec
  allocVecGrowLb allocVecGrowLk
)
open VerifiedLibraries.RustStd.Io (
  allocCallPreserved_of_seg allocCallPreserved_trans
)
open LibsignalBinary.Proofs.SignalSession.CliIo.Sym (
  CliIoPlacement cliIoMpl CliIoBlockNoExtern
  sepWP_seg_cliIo_block_pure
  cliIoMemcpySym cliIoFinishGrowSym
  cliIoPl03 cliIoPC03 cliIoBlockNoSvc0_03
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadLoopCommon (
  poolPreserved_of_stdState
  ioFrame_trans ioFrame_of_allocCall
  cliIoCap cliIoCap_zero cliIoCap_succ cliIoCap_strictMono
  cliIoCap_pos cliIoCap_lt_pow63 cliIoCap_lt_pow64 not_nullAllowed_cliIoCap
  allocVecGrowLb_from_zero allocVecGrowLk_from_zero allocVecGrowLb_telescopes allocVecGrowLk_from_pos
  wantBytes bv64_ult_ofNat_true bv64_ult_ofNat_false bv64_beq_ofNat_false
  bv64_shiftLeft1_ofNat bv64_sub_ofNat wantBytes_csel_bv
  cliIoSavedRegs12
  ioVecBuf_unpack_pos ioVecBuf_repack_chunk stackBuf4096_repack
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadStdinSteps (
  CliIoMidPreserved
)
open LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileSteps (
  cliIo3_lt cliIoReadFile_memcpy_pc cliIoReadFile_grow_pc readReg32_of_readReg64_eq
)

section
arm64_proof_prelude

private theorem sepConj_pure_mid (P Q : SepProp) (φ : Prop) :
    P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) := by
  rw [← sepConj_assoc, sepConj_comm P ⌜φ⌝, sepConj_assoc]

private theorem cliIoFile_cap_clamp_bv {j : Nat} (hj : j ≤ 9) :
    (if (BitVec.ofNat 64 (cliIoCap j)).ult 2097152#64 = true
     then BitVec.ofNat 64 (cliIoCap j)
     else 2097152#64) = BitVec.ofNat 64 (cliIoCap j) := by
  have h2097 : (2097152#64 : BitVec 64) = BitVec.ofNat 64 2097152 := rfl
  rw [h2097]
  rcases Nat.lt_or_eq_of_le hj with hlt | rfl
  · have hlt_cap : cliIoCap j < 2097152 := cliIoCap_strictMono hlt
    rw [bv64_ult_ofNat_true hlt_cap (by decide)]
    rfl
  · rfl

/-- Shared `finish_grow` call + `+0x1b4 .. +0x1c4 → +0x15c = 348#64` join for `read_file`. -/
theorem cliIoReadFile_post_grow [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    {s0 sm_fg : State} {fd sret v0 v1 v2 oldCap oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {newCap len n stackBytes lb_in lk_in : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hnew_pos : 0 < newCap) (hnew_lt63 : newCap < 2 ^ 63)
    (hbs_le : bs.length ≤ newCap) (hno_null : ¬ NullAllowed newCap 1)
    (hcan : A.CanAlloc lb_in lk_in newCap 1)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sm_fg.mem)
    (hpc : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
    (hrun : sm_fg.status = .Running) (hsp0 : s0.spAligned = true)
    (hsp_eq : sm_fg.sp = s0.sp - 8320#64) (hlr : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64)
    (hx0 : sm_fg.readReg64 .x0 = s0.sp - 128#64)
    (hx1 : sm_fg.readReg64 .x1 = oldCap) (hx2 : sm_fg.readReg64 .x2 = oldPtr)
    (hx3 : sm_fg.readReg64 .x3 = BitVec.ofNat 64 newCap)
    (hw19 : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx22 : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap)
    (hx23 : sm_fg.readReg64 .x23 = BitVec.ofNat 64 n)
    (hx24 : sm_fg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sm_fg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sm_fg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp : sm_fg.tpidrEl0 = s0.tpidrEl0) (hvregs : calleeSavedVRegs sm_fg = calleeSavedVRegs s0)
    (hoom_fg : ∀ (sm sf_oom : State),
      IoFrame sm_fg sm → sm.fs = sm_fg.fs → oom sm sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sm_fg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool (allocVecGrowLb A lb_in oldCap.toNat newCap) (allocVecGrowLk lk_in oldCap.toNat) sc ∗
          StdErrnoCell s0.tpidrEl0)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sm_fg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ ioVecBuf A oldCap oldPtr bs ∗
        A.pool lb_in lk_in sm_fg ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  have hnew_lt64 : newCap < 2 ^ 64 := Nat.lt_trans hnew_lt63 (by decide)
  have hsp_fg : sm_fg.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hfg_stk_le : 32 + Rust.hookStack ≤ stackBytes - 8320 := by dsimp [Rust.hookStack] at *; omega
  have hfg_stk_hi : stackBytes - 8320 ≤ 2 ^ 64 := by omega
  wp_conv_pre =>
    rw [stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + Rust.hookStack)
      hfg_stk_le hfg_stk_hi]
  apply seqCodeLoaded hcl (mid := cliIoPl03.base + 436#64)
  apply (SepWP.call_subroutine_frame hfg
    (x := (s0.sp - 128#64, st0, st1, st2, oldCap, oldPtr, bs, newCap, lb_in, lk_in))
    hpc hrun hsp_fg hlr
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun R_oom sf_oom _ hm_oom => by
      have hm' := Satisfies.drop_mid hm_oom
      dsimp only [MultiPlacedLib.withCodeLoaded, allocFinishGrowSpec] at hm'
      rcases (satisfies_pure_sepConj _ _ _).mp hm' with ⟨⟨sm, hif, hfs_eq, hoom_s⟩, hm_r⟩
      have hent := hoom_fg sm sf_oom hif hfs_eq hoom_s
      rw [← emp_sepConj R_oom] at hm_r
      exact Satisfies.mono (sepConj_mono_left hent) hm_r))
  · intro R' hm'
    dsimp only [MultiPlacedLib.withCodeLoaded, allocFinishGrowSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnew_pos, hnew_lt64, hbs_le, fun _ => hcan⟩, ?_⟩
    rw [htp, hsp_eq]
    have hcl_true : (⌜signalSessionIoMultiLib.CodeLoaded cliIoMpl sm_fg.mem⌝ : SepProp) = emp := by
      simp [hcl]
    rw [hcl_true, emp_sepConj]
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_fg' hpc_fg' hrun_fg' hsp_fg' hcs_fg'
    refine SepWP.done hpc_fg' hrun_fg' fun hcl_fg' => ?_
    wp_conv_pre =>
      dsimp only [MultiPlacedLib.withCodeLoaded, allocFinishGrowSpec]
      simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro isErr
    apply SepWP.exists_left; intro newPtr
    apply SepWP.exists_left; intro errW1
    apply SepWP.exists_left; intro errW2
    apply SepWP.pure_elim; intro hacp_fg
    cases isErr with
    | true =>
      wp_conv_pre =>
        simp only [↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + Rust.hookStack))]
        simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_left; intro _ev
      wp_conv_pre =>
        rw [sepConj_comm (stdErrnoAddr sm_fg.tpidrEl0 ↦₃₂ _ev), sepConj_assoc]
      apply SepWP.pure_elim; intro hnull
      exact False.elim (hno_null hnull)
    | false =>
      wp_conv_pre =>
        simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepConj_assoc]
        rw [sepConj_comm (stackAt sm_fg.sp (32 + Rust.hookStack))]
        simp only [sepExists_sepConj_left, sepConj_assoc]
      apply SepWP.exists_left; intro ev
      wp_conv_pre =>
        rw [sepConj_comm (stdErrnoAddr sm_fg.tpidrEl0 ↦₃₂ ev), sepConj_assoc]
      apply SepWP.pure_elim; intro _hnew_lt63'
      have hsp_fg'_eq : sm_fg'.sp = s0.sp - 8320#64 := hsp_fg'.trans hsp_eq
      have hx29_fg' : sm_fg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        hcs_fg'.readReg64_x29.trans hx29
      apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_fg'
        (mid := cliIoPl03.base + 348#64)
      intro sj' hcpu_j0
      have hcpu_j := hcpu_j0.1
      change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
      have hpc_j' : sj'.pc = cliIoPl03.base + 436#64 := hcpu_j.pc_eq.trans hpc_fg'
      have hrun_j' : sj'.status = .Running := hcpu_j.status_eq.trans hrun_fg'
      have hsp_j' : sj'.spAligned = true := by
        rw [hcpu_j.spAligned]; simp only [State.spAligned]; rw [hsp_fg'_eq]
        exact s0.spAligned_sub 8320#64 hsp0
      have hx29_j' : sj'.readReg64 (.gpr 29#5) = s0.sp - 96#64 :=
        (hcpu_j.readReg64 _).trans hx29_fg'
      wp_conv_pre =>
        rw [show vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) =
          ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
          ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      wp_sym_steps
      refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_j')
        fun sc hcpu_c0 hcl_c hnsp_c hsym_c => ?_
      have hcpu_c := hcpu_c0.1
      have ⟨hacp_jc, hpool_jc⟩ :=
        allocCallPreserved_of_seg hcpu_j0 hcpu_c0 hnsp_c hsym_c
          (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      have hpool_eq_jc :
          A.pool (allocVecGrowLb A lb_in oldCap.toNat newCap) (allocVecGrowLk lk_in oldCap.toNat) sm_fg' =
          A.pool (allocVecGrowLb A lb_in oldCap.toNat newCap) (allocVecGrowLk lk_in oldCap.toNat) sc :=
        (A.pool_transport _ _ sm_fg' sc hpool_jc).symm
      have hpc_c : sc.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans (by simp [arm64_norm])
      have hrun_c : sc.status = .Running := hcpu_c.status_eq.trans hrun_j'
      have hsp_c : sc.sp = s0.sp - 8320#64 :=
        hcpu_c.sp_eq.trans ((by simp [arm64_norm] : _ = sj'.sp).trans (hcpu_j.sp_eq.trans hsp_fg'_eq))
      have hw19_c : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
        rw [readReg32_of_readReg64_eq (hcpu_c.readReg64 (.gpr 19#5))]
        simp only [arm64_norm]
        rw [hcpu_j.readReg64 (.gpr 19#5), hcs_fg'.readReg64_x19]
        exact hw19
      have hx20_c : sc.readReg64 (.gpr 20#5) = newPtr := by
        rw [hcpu_c.readReg64]; simp [arm64_norm]
      have hx22_c : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 newCap := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x22.trans hx22)
      have hx23_c : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x23.trans hx23)
      have hx24_c : sc.readReg64 (.gpr 24#5) = sret := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x24.trans hx24)
      have hx25_c : sc.readReg64 (.gpr 25#5) = 4096#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x25.trans hx25)
      have hx26_c : sc.readReg64 (.gpr 26#5) = 2097152#64 := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x26.trans hx26)
      have hx27_c : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x27.trans hx27)
      have hx28_c : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
        rw [hcpu_c.readReg64]; simp only [arm64_norm]
        exact (hcpu_j.readReg64 _).trans (hcs_fg'.readReg64_x28.trans hx28)
      have hx29_c : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
        rw [hcpu_c.readReg64]; simp [arm64_norm, hx29_j']
      have hvregs_c : calleeSavedVRegs sc = calleeSavedVRegs s0 :=
        hcpu_c.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sj').trans
          (hcpu_j.calleeSavedVRegs.trans (hcs_fg'.vregs.trans hvregs)))
      have hacp_all : AllocCallPreserved sm_fg sc := allocCallPreserved_trans hacp_fg hacp_jc
      refine SepWP.weaken_pre ?_
        (hcont sc newPtr newPtr (BitVec.ofNat 64 newCap)
          hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c hx26_c hx27_c hx28_c hx29_c
          hvregs_c hcl_c hacp_all)
      rw [hpool_eq_jc, htp, hsp_eq,
        stackAt_shrink (s0.sp - 8320#64) (stackBytes - 8320) (32 + Rust.hookStack)
          hfg_stk_le hfg_stk_hi,
        show ((s0.sp - 128#64) ↦₆₄ 0#64) ∗ ((s0.sp - 120#64) ↦₆₄ newPtr) ∗
            ((s0.sp - 112#64) ↦₆₄ BitVec.ofNat 64 newCap) =
          vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) by
            simp only [vecHeader, bv_lin_norm]]
      have hev : (stdErrnoAddr s0.tpidrEl0 ↦₃₂ ev) ⊢ StdErrnoCell s0.tpidrEl0 :=
        Entails.sepExists_right ev (Entails.refl _)
      let Rest : SepProp :=
        vecHeader (s0.sp - 128#64) 0#64 newPtr (BitVec.ofNat 64 newCap) ∗
          ioVecBuf A (BitVec.ofNat 64 newCap) newPtr bs ∗
          A.pool (allocVecGrowLb A lb_in oldCap.toNat newCap) (allocVecGrowLk lk_in oldCap.toNat) sc ∗
          memRegion (s0.sp - 8320#64 - BitVec.ofNat 64 (stackBytes - 8320))
            (stackBytes - 8320 - (32 + Rust.hookStack)) ∗
          R_buf ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗ cliIoSavedRegs12 s0 ∗
          vecHeader sret v0 v1 v2 ∗ stackAt (s0.sp - 8320#64) (32 + Rust.hookStack)
      refine Entails.trans ?_
        (Entails.trans (sepConj_mono_right (P := Rest) hev) (by dsimp only [Rest]; sep_entail))
      dsimp only [Rest]; sep_entail

/-- `cap = 0` growth branch of `read_file` (`+0x124 = 292#64 .. +0x1b0` → `post_grow` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_zero [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {R_buf : SepProp} {n stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (_hn_pos : 0 < n) (hn_le : n ≤ 4096)
    (hcan0 : A.CanAlloc lb lk 4096 1)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = 0#64)
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n)
    (hx28 : sg.readReg64 (.gpr 28#5) = 0#64)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp : sg.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ (sm sf_oom : State),
      IoFrame sg sm → sm.fs = sg.fs → oom sm sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 28#5) = 0#64 →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 (cliIoCap 0)) newPtr [] ∗
          A.pool (lb + A.cost (cliIoCap 0) 1) (lk + 1) sc ∗
          StdErrnoCell s0.tpidrEl0)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗ ioVecBuf A 0#64 oldPtr [] ∗
        A.pool lb lk sg ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  have hult_false : (4096#64 : BitVec 64).ult (BitVec.ofNat 64 n) = false :=
    bv64_ult_ofNat_false hn_le (by decide)
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = 0#64 := (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = 0#64 := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hpool_gfg⟩ :=
    allocCallPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg : A.pool lb lk sg = A.pool lb lk sm_fg :=
    (A.pool_transport _ _ sg sm_fg hpool_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = 0#64 := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm, cliIoCap_zero]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap 0) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, cliIoCap_zero]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (0 + n) := by
    rw [hcpu_fg.readReg64]; simpa [arm64_norm] using hx27_g'
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 0 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have htp_fg : sm_fg.tpidrEl0 = s0.tpidrEl0 := hacp_gfg.2.2.2.1.trans htp
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow A hext3 hfg hlo hhi
    (by decide : 0 < cliIoCap 0) (cliIoCap_lt_pow63 (by decide))
    (Nat.zero_le _) (not_nullAllowed_cliIoCap (by decide))
    (by simpa [cliIoCap_zero] using hcan0)
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    htp_fg hvregs_fg
    (fun sm sf_oom hif hfs_eq hoom_s =>
      hoom_sg sm sf_oom (ioFrame_trans (ioFrame_of_allocCall hacp_gfg) hif)
        (hfs_eq.trans hacp_gfg.1) hoom_s)
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc => by
      simpa [Nat.zero_add, allocVecGrowLb_from_zero, allocVecGrowLk_from_zero] using
        hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
          hx25_c hx26_c (by simpa using hx27_c) (by simpa using hx28_c) hx29_c hvregs_c hcl_c
          (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- `cap = cliIoCap j` growth branch of `read_file` (`+0x124 = 292#64 .. +0x1b0` → `post_grow` → `+0x15c = 348#64`). -/
theorem cliIoReadFile_grow_from_pos [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hfg : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
      (signalSessionIoMultiLib.withCodeLoaded cliIoMpl (allocFinishGrowSpec A)))
    {s0 sg : State} {fd sret v0 v1 v2 oldPtr st0 st1 st2 st3 : BitVec 64}
    {bs : List (BitVec 8)} {R_buf : SepProp}
    {j len n stackBytes lb lk : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hlo : 8352 + Rust.hookStack ≤ stackBytes) (hhi : stackBytes ≤ 2 ^ 64)
    (hj1 : j + 1 ≤ 9)
    (hlen_le_cap : len ≤ cliIoCap j)
    (hbs_len : bs.length = len)
    (hgt_cap : cliIoCap j < len + n)
    (hle_next : len + n ≤ cliIoCap (j + 1))
    (hcan_succ : A.CanAlloc (lb + A.cost (cliIoCap j) 1) (lk + 1) (cliIoCap (j + 1)) 1)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sg.mem)
    (hpc : sg.pc = cliIoPl03.base + 292#64) (hrun : sg.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sg.sp = s0.sp - 8320#64)
    (hx0 : sg.readReg64 .x0 = BitVec.ofNat 64 n)
    (hw19 : (sg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sg.readReg64 (.gpr 20#5) = oldPtr)
    (hx21 : sg.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j))
    (hx24 : sg.readReg64 (.gpr 24#5) = sret)
    (hx25 : sg.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sg.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n))
    (hx28 : sg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sg.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (htp : sg.tpidrEl0 = s0.tpidrEl0)
    (hvregs : calleeSavedVRegs sg = calleeSavedVRegs s0)
    (hoom_sg : ∀ (sm sf_oom : State),
      IoFrame sg sm → sm.fs = sg.fs → oom sm sf_oom → emp ⊢ oomProp sf_oom)
    (hcont : ∀ (sc : State) (newPtr st1' st2' : BitVec 64),
      sc.pc = cliIoPl03.base + 348#64 → sc.status = .Running → sc.sp = s0.sp - 8320#64 →
      (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sc.readReg64 (.gpr 20#5) = newPtr →
      sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) →
      sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n →
      sc.readReg64 (.gpr 24#5) = sret →
      sc.readReg64 (.gpr 25#5) = 4096#64 → sc.readReg64 (.gpr 26#5) = 2097152#64 →
      sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) →
      sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len →
      sc.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sc = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem → AllocCallPreserved sg sc →
      SepWP P (s0.readReg64 .lr) sc
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
          vecHeader (s0.sp - 128#64) 0#64 st1' st2' ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 (cliIoCap (j + 1))) newPtr bs ∗
          A.pool (lb + A.cost (cliIoCap (j + 1)) 1) (lk + 1) sc ∗
          StdErrnoCell s0.tpidrEl0)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sg
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_buf ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 (cliIoCap j)) oldPtr bs ∗
        A.pool (lb + A.cost (cliIoCap j) 1) (lk + 1) sg ∗
        StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  have hj9 : j ≤ 9 := by omega
  have hcap_pos : 0 < cliIoCap j := cliIoCap_pos j
  have hcap_lt64 : cliIoCap j < 2 ^ 64 := cliIoCap_lt_pow64 hj9
  have hnext_lt64 : cliIoCap (j + 1) < 2 ^ 64 := cliIoCap_lt_pow64 hj1
  have hcap_beq0 : (BitVec.ofNat 64 (cliIoCap j) == 0#64) = false :=
    bv64_beq_ofNat_false (by omega) hcap_lt64 (by decide)
  have hlsl1 : (BitVec.ofNat 64 (cliIoCap j)) <<< 1 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [bv64_shiftLeft1_ofNat (by rw [← cliIoCap_succ]; exact hnext_lt64), ← cliIoCap_succ]
  have hult1 : (BitVec.ofNat 64 (cliIoCap j)).ult (BitVec.ofNat 64 (len + n)) = true :=
    bv64_ult_ofNat_true hgt_cap (Nat.lt_of_le_of_lt hle_next hnext_lt64)
  have hult2 : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 (len + n)) = false :=
    bv64_ult_ofNat_false hle_next hnext_lt64
  have hclamp :
      (if (BitVec.ofNat 64 (cliIoCap (j + 1))).ult 2097152#64 = true
       then BitVec.ofNat 64 (cliIoCap (j + 1))
       else 2097152#64) = BitVec.ofNat 64 (cliIoCap (j + 1)) :=
    cliIoFile_cap_clamp_bv hj1
  have hcap_lt_next : cliIoCap j < cliIoCap (j + 1) := cliIoCap_strictMono (Nat.lt_succ_self j)
  have hsub_hi :
      (BitVec.ofNat 64 (cliIoCap j) - BitVec.ofNat 64 len).ult
        (BitVec.ofNat 64 (cliIoCap (j + 1)) - BitVec.ofNat 64 len) = true := by
    rw [bv64_sub_ofNat hlen_le_cap, bv64_sub_ofNat (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next))]
    exact bv64_ult_ofNat_true (by omega) (by omega)
  have hnext_ult_len : (BitVec.ofNat 64 (cliIoCap (j + 1))).ult (BitVec.ofNat 64 len) = false :=
    bv64_ult_ofNat_false (Nat.le_trans hlen_le_cap (Nat.le_of_lt hcap_lt_next)) hnext_lt64
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym)
  intro sg' hcpu_g0
  have hcpu_g := hcpu_g0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_g' : sg'.pc = cliIoPl03.base + 292#64 := hcpu_g.pc_eq.trans hpc
  have hrun_g' : sg'.status = .Running := hcpu_g.status_eq.trans hrun
  have hsp_g' : sg'.spAligned = true := by
    rw [hcpu_g.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx0_g' : sg'.readReg64 .x0 = BitVec.ofNat 64 n := (hcpu_g.readReg64 _).trans hx0
  have hx20_g' : sg'.readReg64 (.gpr 20#5) = oldPtr := (hcpu_g.readReg64 _).trans hx20
  have hx21_g' : sg'.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (cliIoCap j) :=
    (hcpu_g.readReg64 _).trans hx21
  have hx24_g' : sg'.readReg64 (.gpr 24#5) = sret := (hcpu_g.readReg64 _).trans hx24
  have hx25_g' : sg'.readReg64 (.gpr 25#5) = 4096#64 := (hcpu_g.readReg64 _).trans hx25
  have hx26_g' : sg'.readReg64 (.gpr 26#5) = 2097152#64 := (hcpu_g.readReg64 _).trans hx26
  have hx27_g' : sg'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) :=
    (hcpu_g.readReg64 _).trans hx27
  have hx28_g' : sg'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := (hcpu_g.readReg64 _).trans hx28
  have hx29_g' : sg'.readReg64 (.gpr 29#5) = s0.sp - 96#64 := (hcpu_g.readReg64 _).trans hx29
  wp_sym_steps
  refine SepWP.done cliIoReadFile_grow_pc (by simpa [arm64_norm] using hrun_g')
    fun sm_fg hcpu_fg0 hcl_fg hnsp_fg hsym_fg => ?_
  have hcpu_fg := hcpu_fg0.1
  have ⟨hacp_gfg, hpool_gfg⟩ :=
    allocCallPreserved_of_seg hcpu_g0 hcpu_fg0 hnsp_fg hsym_fg
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_gfg :
      A.pool (lb + A.cost (cliIoCap j) 1) (lk + 1) sg =
      A.pool (lb + A.cost (cliIoCap j) 1) (lk + 1) sm_fg :=
    (A.pool_transport _ _ sg sm_fg hpool_gfg).symm
  have hpc_fg : sm_fg.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoFinishGrowSym :=
    hcpu_fg.pc_eq.trans cliIoReadFile_grow_pc
  have hrun_fg : sm_fg.status = .Running := hcpu_fg.status_eq.trans hrun_g'
  have hsp_fg : sm_fg.sp = s0.sp - 8320#64 :=
    hcpu_fg.sp_eq.trans ((by simp [arm64_norm] : _ = sg'.sp).trans (hcpu_g.sp_eq.trans hsp_eq))
  have hlr_fg : sm_fg.readReg64 .lr = cliIoPl03.base + 436#64 := by
    rw [hcpu_fg.readReg64 .lr]; simp [arm64_norm]
  have hx0_fg : sm_fg.readReg64 .x0 = s0.sp - 128#64 := by
    rw [hcpu_fg.readReg64 .x0]; simp [arm64_norm]
  have hx1_fg : sm_fg.readReg64 .x1 = BitVec.ofNat 64 (cliIoCap j) := by
    rw [hcpu_fg.readReg64 .x1]; simp [arm64_norm]
  have hx2_fg : sm_fg.readReg64 .x2 = oldPtr := by
    rw [hcpu_fg.readReg64 .x2]; simp [arm64_norm]
  have hx3_fg : sm_fg.readReg64 .x3 = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64 .x3]; simp [arm64_norm]
  have hw19_fg : (sm_fg.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
    rw [readReg32_of_readReg64_eq (hcpu_fg.readReg64 (.gpr 19#5))]
    simp only [arm64_norm]
    rw [hcpu_g.readReg64 (.gpr 19#5)]
    exact hw19
  have hx22_fg : sm_fg.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (cliIoCap (j + 1)) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx23_fg : sm_fg.readReg64 (.gpr 23#5) = BitVec.ofNat 64 n := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm]
  have hx24_fg : sm_fg.readReg64 (.gpr 24#5) = sret := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx24_g']
  have hx25_fg : sm_fg.readReg64 (.gpr 25#5) = 4096#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx25_g']
  have hx26_fg : sm_fg.readReg64 (.gpr 26#5) = 2097152#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx26_g']
  have hx27_fg : sm_fg.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + n) := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx27_g']
  have hx28_fg : sm_fg.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx28_g']
  have hx29_fg : sm_fg.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcpu_fg.readReg64]; simp [arm64_norm, hx29_g']
  have htp_fg : sm_fg.tpidrEl0 = s0.tpidrEl0 := hacp_gfg.2.2.2.1.trans htp
  have hvregs_fg : calleeSavedVRegs sm_fg = calleeSavedVRegs s0 :=
    hcpu_fg.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sg').trans
      (hcpu_g.calleeSavedVRegs.trans hvregs))
  have hcap_toNat : (BitVec.ofNat 64 (cliIoCap j)).toNat = cliIoCap j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt64]
  rw [hpool_eq_gfg]
  exact cliIoReadFile_post_grow A hext3 hfg hlo hhi
    (cliIoCap_pos (j + 1)) (cliIoCap_lt_pow63 hj1)
    (by rw [hbs_len]; omega) (not_nullAllowed_cliIoCap hj1) hcan_succ
    hcl_fg hpc_fg hrun_fg hsp0 hsp_fg hlr_fg
    hx0_fg hx1_fg hx2_fg hx3_fg hw19_fg hx22_fg hx23_fg hx24_fg hx25_fg hx26_fg hx27_fg hx28_fg hx29_fg
    htp_fg hvregs_fg
    (fun sm sf_oom hif hfs_eq hoom_s =>
      hoom_sg sm sf_oom (ioFrame_trans (ioFrame_of_allocCall hacp_gfg) hif)
        (hfs_eq.trans hacp_gfg.1) hoom_s)
    (fun sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c hx25_c
        hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c hacp_fgc => by
      rw [hcap_toNat, allocVecGrowLb_telescopes A hcap_pos, allocVecGrowLk_from_pos hcap_pos]
      exact hcont sc newPtr st1' st2' hpc_c hrun_c hsp_c hw19_c hx20_c hx22_c hx23_c hx24_c
        hx25_c hx26_c hx27_c hx28_c hx29_c hvregs_c hcl_c
        (allocCallPreserved_trans hacp_gfg hacp_fgc))

/-- Shared `memcpy(ptr + len, sp + 4096, chunk)` + back-edge `+0x16c .. +0x18c → +0xd8 = 216#64` join. -/
theorem cliIoReadFile_memcpy_backedge [CliIoPlacement]
    {oom : State → State → Prop} (A : RustStdAlloc oom)
    {P : Program} (hext3 : CliIoBlockNoExtern cliIoMpl P 3)
    (hmemcpy : subroutine_ok P (signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym) stdMemcpySpec)
    {s0 sc : State} {fd sret v0 v1 v2 ptr st0 st1 st2 st3 : BitVec 64}
    {R_path : SepProp}
    {rem chunk oldBuf : List (BitVec 8)}
    {cap len want stackBytes lb_cur lk_cur : Nat}
    {post : State → SepProp → Prop} {oomProp : State → SepProp}
    (hcap_pos : 0 < cap) (hcap_lt63 : cap < 2 ^ 63)
    (hlen_r : len + chunk.length ≤ rem.length)
    (hlen_cap : len + chunk.length ≤ cap)
    (hlen_max : len + chunk.length ≤ 2097152)
    (hwant_le : want ≤ 4096)
    (hold_len : oldBuf.length = want)
    (hn_le_want : chunk.length ≤ want)
    (hchunk_eq : chunk = (rem.drop len).take want)
    (hcl : signalSessionIoMultiLib.CodeLoaded cliIoMpl sc.mem)
    (hpc : sc.pc = cliIoPl03.base + 348#64) (hrun : sc.status = .Running)
    (hsp0 : s0.spAligned = true) (hsp_eq : sc.sp = s0.sp - 8320#64)
    (hw19 : (sc.readReg32 (.gpr 19#5)).zeroExtend 64 = fd)
    (hx20 : sc.readReg64 (.gpr 20#5) = ptr)
    (hx22 : sc.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap)
    (hx23 : sc.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length)
    (hx24 : sc.readReg64 (.gpr 24#5) = sret)
    (hx25 : sc.readReg64 (.gpr 25#5) = 4096#64)
    (hx26 : sc.readReg64 (.gpr 26#5) = 2097152#64)
    (hx27 : sc.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length))
    (hx28 : sc.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len)
    (hx29 : sc.readReg64 (.gpr 29#5) = s0.sp - 96#64)
    (hvregs : calleeSavedVRegs sc = calleeSavedVRegs s0)
    (hcont : ∀ sn : State,
      sn.pc = cliIoPl03.base + 216#64 → sn.status = .Running → sn.sp = s0.sp - 8320#64 →
      (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd →
      sn.readReg64 (.gpr 20#5) = ptr →
      sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap →
      sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) →
      sn.readReg64 (.gpr 24#5) = sret →
      sn.readReg64 (.gpr 25#5) = 4096#64 →
      sn.readReg64 (.gpr 26#5) = 2097152#64 →
      sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) →
      sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 → calleeSavedVRegs sn = calleeSavedVRegs s0 →
      signalSessionIoMultiLib.CodeLoaded cliIoMpl sn.mem → CliIoMidPreserved sc sn →
      SepWP P (s0.readReg64 .lr) sn
        (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
          memRegion (s0.sp - 4224#64) 4096 ∗
          vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
          cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
          ioVecBuf A (BitVec.ofNat 64 cap) ptr (rem.take (len + chunk.length)) ∗
          A.pool lb_cur lk_cur sn ∗ StdErrnoCell s0.tpidrEl0)
        post oomProp) :
    SepWP P (s0.readReg64 .lr) sc
      (stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        (((s0.sp - 4224#64) ↦ₛ (chunk ++ oldBuf.drop chunk.length)) ∗
          memRegion (s0.sp - 4224#64 + BitVec.ofNat 64 want) (4096 - want)) ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        ioVecBuf A (BitVec.ofNat 64 cap) ptr (rem.take len) ∗
        A.pool lb_cur lk_cur sc ∗ StdErrnoCell s0.tpidrEl0)
      post oomProp := by
  have htake_len : (rem.take len).length = len := List.length_take_of_le (by omega)
  wp_conv_pre =>
    rw [ioVecBuf_unpack_pos A hcap_pos hcap_lt63]
    simp only [sepConj_assoc, sepConj_pure_mid]
  apply SepWP.pure_elim; rintro ⟨_, _, hptr_ne0⟩
  wp_conv_pre =>
    rw [htake_len,
      memRegion_split_le (ptr + BitVec.ofNat 64 len) chunk.length (cap - len) (by omega) (by omega),
      show ptr + BitVec.ofNat 64 len + BitVec.ofNat 64 chunk.length =
        ptr + BitVec.ofNat 64 (len + chunk.length) by rw [BitVec.ofNat_add]; bv_lin,
      show cap - len - chunk.length = cap - (len + chunk.length) by omega,
      pointsToBytes_append (s0.sp - 4224#64) chunk (oldBuf.drop chunk.length)]
    simp only [sepConj_assoc]
  apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl
    (mid := signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym)
  intro sc' hcpu_c0
  have hcpu_c := hcpu_c0.1
  change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
  have hpc_c' : sc'.pc = cliIoPl03.base + 348#64 := hcpu_c.pc_eq.trans hpc
  have hrun_c' : sc'.status = .Running := hcpu_c.status_eq.trans hrun
  have hsp_c_in : sc'.sp = s0.sp - 8320#64 := hcpu_c.sp_eq.trans hsp_eq
  have hsp_c' : sc'.spAligned = true := by
    rw [hcpu_c.spAligned]; simp only [State.spAligned]; rw [hsp_eq]
    exact s0.spAligned_sub 8320#64 hsp0
  have hx20_c' : sc'.readReg64 (.gpr 20#5) = ptr := (hcpu_c.readReg64 _).trans hx20
  have hx23_c' : sc'.readReg64 (.gpr 23#5) = BitVec.ofNat 64 chunk.length :=
    (hcpu_c.readReg64 _).trans hx23
  have hx28_c' : sc'.readReg64 (.gpr 28#5) = BitVec.ofNat 64 len :=
    (hcpu_c.readReg64 _).trans hx28
  wp_sym_steps
  refine SepWP.done cliIoReadFile_memcpy_pc (by simpa [arm64_norm] using hrun_c')
    fun sm_mc hcpu_mc0 hcl_mc hnsp_mc hsym_mc => ?_
  have hcpu_mc := hcpu_mc0.1
  have ⟨hacp_cmc, hpool_cmc⟩ :=
    allocCallPreserved_of_seg hcpu_c0 hcpu_mc0 hnsp_mc hsym_mc
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
  have hpool_eq_cmc : A.pool lb_cur lk_cur sc = A.pool lb_cur lk_cur sm_mc :=
    (A.pool_transport _ _ sc sm_mc hpool_cmc).symm
  have hpc_mc : sm_mc.pc = signalSessionIoMultiLib.resolve cliIoMpl cliIoMemcpySym :=
    hcpu_mc.pc_eq.trans cliIoReadFile_memcpy_pc
  have hrun_mc : sm_mc.status = .Running := hcpu_mc.status_eq.trans hrun_c'
  have hsp_mc_eq : sm_mc.sp = s0.sp - 8320#64 :=
    hcpu_mc.sp_eq.trans ((by simp [arm64_norm] : _ = sc'.sp).trans hsp_c_in)
  have hsp_mc : sm_mc.spAligned = true := by
    simp only [State.spAligned]; rw [hsp_mc_eq]; exact s0.spAligned_sub 8320#64 hsp0
  have hlr_mc : sm_mc.readReg64 .lr = cliIoPl03.base + 364#64 := by
    rw [hcpu_mc.readReg64 .lr]; simp [arm64_norm]
  have hx0_mc : sm_mc.readReg64 .x0 = ptr + BitVec.ofNat 64 len := by
    rw [hcpu_mc.readReg64 .x0]; simp [arm64_norm]
  have hx1_mc : sm_mc.readReg64 .x1 = s0.sp - 4224#64 := by
    rw [hcpu_mc.readReg64 .x1]; simp only [arm64_norm]
  have hx2_mc : sm_mc.readReg64 .x2 = BitVec.ofNat 64 chunk.length := by
    rw [hcpu_mc.readReg64 .x2]; simp [arm64_norm, hchunk_eq]
  apply seqCodeLoaded hcl_mc (mid := cliIoPl03.base + 364#64)
  apply (SepWP.call_subroutine_frame hmemcpy
    (x := (ptr + BitVec.ofNat 64 len, s0.sp - 4224#64, chunk))
    hpc_mc hrun_mc hsp_mc hlr_mc
    (h_no_panic := fun _ _ _ h => not_satisfies_false_sepConj h)
    (h_no_exit := fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (h_oom := fun _ _ _ h => False.elim (not_satisfies_false_sepConj h)))
  · intro R' hm'
    dsimp only [stdMemcpySpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    have hchunk_lt64 : chunk.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.le_trans hn_le_want hwant_le) (by decide)
    refine ⟨⟨hx0_mc, hx1_mc, hx2_mc, hchunk_lt64⟩, ?_⟩
    rw [hpool_eq_cmc] at hm'
    exact Satisfies.mono (by sep_frame) hm'
  · intro sm_mc' hpc_mc' hrun_mc' hsp_mc' hcs_mc'
    refine SepWP.done hpc_mc' hrun_mc' fun hcl_mc' => ?_
    wp_conv_pre => dsimp only [stdMemcpySpec]; simp only [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨_, hstd_mc⟩
    have hmid_mc : CliIoMidPreserved sm_mc sm_mc' := CliIoMidPreserved.of_std hstd_mc
    have hpool_eq_mc : A.pool lb_cur lk_cur sm_mc = A.pool lb_cur lk_cur sm_mc' :=
      (A.pool_transport _ _ sm_mc sm_mc' (poolPreserved_of_stdState hstd_mc)).symm
    have hsp_mc'_eq : sm_mc'.sp = s0.sp - 8320#64 := hsp_mc'.trans hsp_mc_eq
    have hx22_mc' : sm_mc'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      hcs_mc'.readReg64_x22.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 22#5)).trans
          ((hcpu_c.readReg64 _).trans hx22)))
    have hx25_mc' : sm_mc'.readReg64 (.gpr 25#5) = 4096#64 :=
      hcs_mc'.readReg64_x25.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 25#5)).trans
          ((hcpu_c.readReg64 _).trans hx25)))
    have hx27_mc' : sm_mc'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      hcs_mc'.readReg64_x27.trans ((hcpu_mc.readReg64 _).trans
        ((by simp [arm64_norm] : _ = sc'.readReg64 (.gpr 27#5)).trans
          ((hcpu_c.readReg64 _).trans hx27)))
    have hsub8 :
        2097153#64 - BitVec.ofNat 64 (len + chunk.length) =
          BitVec.ofNat 64 (2097152 + 1 - (len + chunk.length)) := by
      change BitVec.ofNat 64 2097153 - BitVec.ofNat 64 (len + chunk.length) = _
      exact bv64_sub_ofNat (by omega)
    have hule :
        (BitVec.ofNat 64 (len + ((rem.drop len).take want).length)).ule 2097152#64 = true := by
      rw [← hchunk_eq]
      have hlt64 : len + chunk.length < 2 ^ 64 := by omega
      simp [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, hlen_max]
    apply sepWP_seg_cliIo_block_pure 3 cliIo3_lt hext3 cliIoBlockNoSvc0_03 hcl_mc'
      (mid := cliIoPl03.base + 216#64)
    intro sb' hcpu_b0
    have hcpu_b := hcpu_b0.1
    change SepWP (cliIoPC03.rebase cliIoPl03.base (fun _ => none)) _ _ _ _
    have hpc_b' : sb'.pc = cliIoPl03.base + 364#64 := hcpu_b.pc_eq.trans hpc_mc'
    have hrun_b' : sb'.status = .Running := hcpu_b.status_eq.trans hrun_mc'
    have hsp_b' : sb'.spAligned = true := by
      rw [hcpu_b.spAligned]; simp only [State.spAligned]; rw [hsp_mc'_eq]
      exact s0.spAligned_sub 8320#64 hsp0
    have hx22_b' : sb'.readReg64 (.gpr 22#5) = BitVec.ofNat 64 cap :=
      (hcpu_b.readReg64 _).trans hx22_mc'
    have hx25_b' : sb'.readReg64 (.gpr 25#5) = 4096#64 :=
      (hcpu_b.readReg64 _).trans hx25_mc'
    have hx27_b' : sb'.readReg64 (.gpr 27#5) = BitVec.ofNat 64 (len + chunk.length) :=
      (hcpu_b.readReg64 _).trans hx27_mc'
    wp_sym_steps
    refine SepWP.done (by simp [arm64_norm]) (by simpa [arm64_norm] using hrun_b')
      fun sn hcpu_n0 hcl_n hnsp_n hsym_n => ?_
    have hcpu_n := hcpu_n0.1
    have ⟨hacp_bn, hpool_bn⟩ :=
      allocCallPreserved_of_seg hcpu_b0 hcpu_n0 hnsp_n hsym_n
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    have hpool_eq_bn : A.pool lb_cur lk_cur sm_mc' = A.pool lb_cur lk_cur sn :=
      (A.pool_transport _ _ sm_mc' sn hpool_bn).symm
    have hpc_n : sn.pc = cliIoPl03.base + 216#64 := by
      rw [hcpu_n.pc_eq]; simp [arm64_norm]
    have hrun_n : sn.status = .Running := hcpu_n.status_eq.trans hrun_b'
    have hsp_n : sn.sp = s0.sp - 8320#64 :=
      hcpu_n.sp_eq.trans ((by simp [arm64_norm] : _ = sb'.sp).trans (hcpu_b.sp_eq.trans hsp_mc'_eq))
    have hw19_n : (sn.readReg32 (.gpr 19#5)).zeroExtend 64 = fd := by
      rw [readReg32_of_readReg64_eq (hcpu_n.readReg64 (.gpr 19#5))]
      simp only [arm64_norm]
      rw [hcpu_b.readReg64 (.gpr 19#5), hcs_mc'.readReg64_x19,
        hcpu_mc.readReg64 (.gpr 19#5)]
      simp only [arm64_norm]
      rw [hcpu_c.readReg64 (.gpr 19#5)]
      exact hw19
    have hx20_n : sn.readReg64 (.gpr 20#5) = ptr := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x20, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact hx20_c'
    have hx21_n : sn.readReg64 (.gpr 21#5) = BitVec.ofNat 64 cap := by
      rw [hcpu_n.readReg64]; simp [arm64_norm]
    have hx23_n : sn.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (wantBytes 2097152 (len + chunk.length)) := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]; rw [← hchunk_eq, hsub8]
      exact wantBytes_csel_bv hlen_max (by decide)
    have hx24_n : sn.readReg64 (.gpr 24#5) = sret := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x24, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx24
    have hx25_n : sn.readReg64 (.gpr 25#5) = 4096#64 := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hx25_b']
    have hx26_n : sn.readReg64 (.gpr 26#5) = 2097152#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x26, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx26
    have hx28_n : sn.readReg64 (.gpr 28#5) = BitVec.ofNat 64 (len + chunk.length) := by
      rw [hcpu_n.readReg64]; simp [arm64_norm, hchunk_eq]
    have hx29_n : sn.readReg64 (.gpr 29#5) = s0.sp - 96#64 := by
      rw [hcpu_n.readReg64]; simp only [arm64_norm]
      rw [hcpu_b.readReg64, hcs_mc'.readReg64_x29, hcpu_mc.readReg64]; simp only [arm64_norm]
      exact (hcpu_c.readReg64 _).trans hx29
    have hvregs_n : calleeSavedVRegs sn = calleeSavedVRegs s0 :=
      hcpu_n.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sb').trans
        (hcpu_b.calleeSavedVRegs.trans (hcs_mc'.vregs.trans
          (hcpu_mc.calleeSavedVRegs.trans ((by simp [arm64_norm] : _ = calleeSavedVRegs sc').trans
            (hcpu_c.calleeSavedVRegs.trans hvregs))))))
    have hmid_cn : CliIoMidPreserved sc sn :=
      (CliIoMidPreserved.of_alloc hacp_cmc).trans
        (hmid_mc.trans (CliIoMidPreserved.of_alloc hacp_bn))
    refine SepWP.weaken_pre ?_
      (hcont sn hpc_n hrun_n hsp_n hw19_n hx20_n hx21_n hx23_n hx24_n hx25_n hx26_n hx28_n hx29_n
        hvregs_n hcl_n hmid_cn)
    rw [hpool_eq_mc, hpool_eq_bn]
    have hvec_back := ioVecBuf_repack_chunk A hcap_pos hcap_lt63 hptr_ne0 hlen_r hlen_cap hchunk_eq
    have hbuf_back := stackBuf4096_repack hwant_le hold_len hn_le_want (buf := s0.sp - 4224#64)
    let Rest : SepProp :=
      stackAt (s0.sp - 8320#64) (stackBytes - 8320) ∗ R_path ∗
        vecHeader (s0.sp - 128#64) st0 st1 st2 ∗ ((s0.sp - 104#64) ↦₆₄ st3) ∗
        cliIoSavedRegs12 s0 ∗ vecHeader sret v0 v1 v2 ∗
        A.pool lb_cur lk_cur sn ∗ StdErrnoCell s0.tpidrEl0
    refine Entails.trans ?_
      (Entails.trans (sepConj_mono_left (Q := Rest) (sepConj_mono hvec_back hbuf_back))
        (by dsimp only [Rest]; sep_entail))
    dsimp only [Rest]; sep_entail

end

end LibsignalBinary.Proofs.SignalSession.CliIo.ReadFileGrowSteps
